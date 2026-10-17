// SHA-384 configuration with proof-size levers (lane/pq-whir-levers).
// Built against stark-backend + patches/stark-backend-levers.patch.
// With every lever at its default (48-B digests, per-row leaves, no grinding) this is
// byte-for-byte the native_sha384_config.rs profile (framing "nearproof-native-sha384-ext12-v4").
// Experimental; compiler applicability remains unproved.
use std::io::{self,Read,Write};
use openvm_stark_backend::{StarkProtocolConfig,FiatShamirTranscript,hasher::MerkleHasher,
    codec::{EncodableConfig,DecodableConfig,encode_prime_field32,decode_prime_field32,encode_extension_field32,decode_extension_field32},
    prover::{ReferenceDevice,Coordinator}};
use p3_field::{extension::BinomialExtensionField,PrimeField32};
use sha2::{Sha384,Digest as ShaDigest};
type F=p3_baby_bear::BabyBear;
type EF=BinomialExtensionField<F,12>;
type Digest=[u64;6];

/// Hash-level levers. Process-global because the backend codec traits are static.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct ShaLevers {
    /// Merkle digest width in bytes: 48 (SHA-384) or 42 (SHA-384 truncated to 336 bits).
    pub(crate) digest_bytes:usize,
    /// Hash each WHIR leaf (all 2^k rows of a fold coset) as one SHA-384 message.
    pub(crate) coset_leaf:bool,
}
impl ShaLevers {
    const DEFAULT:ShaLevers=ShaLevers{digest_bytes:48,coset_leaf:false};
    fn is_default(&self)->bool {*self==Self::DEFAULT}
    /// 32-byte framing prefix of every hash_parts message. Default profile keeps v4; any
    /// lever switches to a v5 prefix that names the digest width and leaf format.
    fn prefix(&self)->[u8;32] {
        let s=if self.is_default() {"nearproof-native-sha384-ext12-v4".to_string()}
            else {format!("nearproof-sha384-ext12-v5-w{:02}-c{}",self.digest_bytes,self.coset_leaf as u8)};
        s.as_bytes().try_into().expect("32-byte prefix")
    }
    /// 8-byte node-compression prefix.
    fn node_prefix(&self)->[u8;8] {
        if self.is_default() {*b"NPQ4NODE"} else {[b'N',b'P',b'Q',b'5',self.digest_bytes as u8,self.coset_leaf as u8,b'N',b'D']}
    }
}
static LEVERS:std::sync::OnceLock<ShaLevers>=std::sync::OnceLock::new();
fn levers()->ShaLevers {*LEVERS.get().unwrap_or(&ShaLevers::DEFAULT)}
pub(crate) fn set_sha_levers(l:ShaLevers) {
    assert!(l.digest_bytes==48 || l.digest_bytes==42,"digest width must be 48 or 42 bytes");
    LEVERS.set(l).expect("SHA levers already set");
}
fn truncate(mut d:[u8;48])->[u8;48] {let w=levers().digest_bytes; for b in &mut d[w..] {*b=0;} d}
fn digest_bytes(d:Digest)->Vec<u8> {d.into_iter().flat_map(u64::to_le_bytes).collect()}
/// The wire/absorbed form of a Merkle digest: its first `digest_bytes` bytes.
fn digest_wire(d:Digest)->Vec<u8> {let mut b=digest_bytes(d);b.truncate(levers().digest_bytes);b}

// Tags: 0 leaf row, 1 node, 2 init, 3 observe, 4 observe_commit, 5 draw, 6 coset leaf, 7 grind.
const NTAGS:usize=8;
static HASH_CALLS:[std::sync::atomic::AtomicU64;NTAGS]=[const {std::sync::atomic::AtomicU64::new(0)};NTAGS];
static HASH_BLOCKS:[std::sync::atomic::AtomicU64;NTAGS]=[const {std::sync::atomic::AtomicU64::new(0)};NTAGS];
static COUNT_GRIND:std::sync::atomic::AtomicBool=std::sync::atomic::AtomicBool::new(true);
static MERKLE_TRACE_ON:std::sync::atomic::AtomicBool=std::sync::atomic::AtomicBool::new(false);
static MERKLE_TRACE:std::sync::Mutex<Vec<u8>>=std::sync::Mutex::new(Vec::new());
fn record_merkle(kind:u8,payload:&[u8],digest:Digest) {
    if MERKLE_TRACE_ON.load(std::sync::atomic::Ordering::Relaxed) {
        let mut log=MERKLE_TRACE.lock().unwrap();
        log.push(kind);log.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        log.extend_from_slice(payload);log.extend(digest_wire(digest));
    }
}
fn hash_counts()->([u64;NTAGS],[u64;NTAGS]) {
    use std::sync::atomic::Ordering::Relaxed;
    (std::array::from_fn(|i|HASH_CALLS[i].load(Relaxed)),std::array::from_fn(|i|HASH_BLOCKS[i].load(Relaxed)))
}
/// SHA-384(prefix32 || tag || (len_le64 || part)*). Blocks counted with standard padding.
fn hash_parts(tag:u8,parts:&[&[u8]])->[u8;48] {
    use std::sync::atomic::Ordering::Relaxed;
    let prefix=levers().prefix();
    let message_len=prefix.len()+1+parts.iter().map(|p|8+p.len()).sum::<usize>();
    if tag!=7 || COUNT_GRIND.load(Relaxed) {
        HASH_CALLS[tag as usize].fetch_add(1,Relaxed);
        HASH_BLOCKS[tag as usize].fetch_add(((message_len+17).div_ceil(128)) as u64,Relaxed);
    }
    let mut h=Sha384::new();h.update(prefix);h.update([tag]);
    for part in parts {h.update((part.len() as u64).to_le_bytes());h.update(part);}
    h.finalize().into()
}
fn words(bytes:[u8;48])->Digest {std::array::from_fn(|i|u64::from_le_bytes(bytes[i*8..i*8+8].try_into().unwrap()))}
fn field_bytes(values:&[F])->Vec<u8> {values.iter().flat_map(|x|x.as_canonical_u32().to_le_bytes()).collect()}
#[derive(Clone,Debug)]
struct ShaHasher;
impl MerkleHasher for ShaHasher {
    type F=F;type Digest=Digest;
    fn hash_slice(&self,values:&[F])->Digest {
        let bytes=field_bytes(values);
        let digest=words(truncate(hash_parts(0,&[&bytes])));record_merkle(0,&bytes,digest);digest
    }
    fn compress(&self,left:Digest,right:Digest)->Digest {
        // Fixed-width, disjoint node domain: 8+2w bytes (<= 104) fits one SHA-384 block.
        use std::sync::atomic::Ordering::Relaxed;
        HASH_CALLS[1].fetch_add(1,Relaxed);HASH_BLOCKS[1].fetch_add(1,Relaxed);
        let (l,r)=(digest_wire(left),digest_wire(right));
        let mut h=Sha384::new();h.update(levers().node_prefix());h.update(&l);h.update(&r);
        let digest=words(truncate(h.finalize().into()));
        record_merkle(1,&[l,r].concat(),digest);digest
    }
    fn hash_coset(&self,rows:&[Vec<F>])->Digest {
        if !levers().coset_leaf {
            return self.tree_compress(rows.iter().map(|row|self.hash_slice(row)).collect());
        }
        // One message: rows t = 0..2^k in coset order, each row's canonical u32 LE words.
        let bytes:Vec<u8>=rows.iter().flat_map(|r|field_bytes(r)).collect();
        let digest=words(truncate(hash_parts(6,&[&bytes])));record_merkle(6,&bytes,digest);digest
    }
}
#[derive(Clone,Debug)]
struct SC {params:SystemParams,hasher:ShaHasher}
impl StarkProtocolConfig for SC {
    type F=F;type EF=EF;type Digest=Digest;type Hasher=ShaHasher;
    fn params(&self)->&SystemParams {&self.params}
    fn hasher(&self)->&ShaHasher {&self.hasher}
}
impl EncodableConfig for SC {
    fn encode_base_field<W:Write>(v:&F,w:&mut W)->io::Result<()> {encode_prime_field32(v,w)}
    fn encode_extension_field<W:Write>(v:&EF,w:&mut W)->io::Result<()> {encode_extension_field32::<F,_,_>(v,w)}
    fn encode_digest<W:Write>(v:&Digest,w:&mut W)->io::Result<()> {w.write_all(&digest_wire(*v))}
}
impl DecodableConfig for SC {
    fn decode_base_field<R:Read>(r:&mut R)->io::Result<F> {decode_prime_field32(r)}
    fn decode_extension_field<R:Read>(r:&mut R)->io::Result<EF> {decode_extension_field32::<F,_,_>(r)}
    fn decode_digest<R:Read>(r:&mut R)->io::Result<Digest> {
        let mut b=[0;48];r.read_exact(&mut b[..levers().digest_bytes])?;Ok(words(b))
    }
}
#[derive(Clone)]
struct Transcript {state:[u8;48],next_word:usize,pending:Vec<u8>}
impl Transcript {
    fn new()->Self {Self {state:hash_parts(2,&[]),next_word:12,pending:Vec::new()}}
    fn flush(&mut self) {
        if !self.pending.is_empty() {
            self.state=hash_parts(3,&[&self.state,&self.pending]);
            self.pending.clear();self.next_word=12;
        }
    }
    /// Proof-of-work step: state' = H(tag 7, state || witness_le32); the witness is valid iff the
    /// first `bits` bits of state' (big-endian bit order of byte 0, 1, ...) are zero. state' becomes
    /// the transcript state, so later challenges are re-hashed from it (tag 5) and never reuse the
    /// PoW bits. One SHA-384 compression per attempt (101-byte message).
    fn pow_step(&self,witness:u32,bits:usize)->([u8;48],bool) {
        let state=hash_parts(7,&[&self.state,&witness.to_le_bytes()]);
        (state,leading_zero_bits(&state)>=bits)
    }
}
fn leading_zero_bits(s:&[u8;48])->usize {
    let mut n=0; for &b in s {if b==0 {n+=8;} else {n+=b.leading_zeros() as usize;break;}} n
}
/// (bits, seconds, minimal witness found) per grind call.
pub(crate) static GRIND_STATS:std::sync::Mutex<Vec<(usize,f64,u64)>>=std::sync::Mutex::new(Vec::new());
impl FiatShamirTranscript<SC> for Transcript {
    fn observe(&mut self,v:F) {self.pending.extend_from_slice(&v.as_canonical_u32().to_le_bytes());self.next_word=12;}
    fn observe_commit(&mut self,d:Digest) {self.flush();self.state=hash_parts(4,&[&self.state,&digest_wire(d)]);self.next_word=12;}
    fn sample(&mut self)->F {
        self.flush();
        loop {
            if self.next_word==12 {self.state=hash_parts(5,&[&self.state]);self.next_word=0;}
            let start=4*self.next_word;self.next_word+=1;
            let n=u32::from_le_bytes(self.state[start..start+4].try_into().unwrap());
            // Exact uniformity for a fresh random 32-bit word, no modulo bias.
            // Rejections advance the buffer cursor; exhausted buffers rehash.
            // Observe operations invalidate unused words. No capped retry or zero fill.
            if n<4026531842 {return F::from_u32(n%2013265921);}
        }
    }
    fn check_witness(&mut self,bits:usize,witness:F)->bool {
        if bits==0 {return true;}
        self.flush();
        let (state,ok)=self.pow_step(witness.as_canonical_u32(),bits);
        self.state=state;self.next_word=12;ok
    }
    fn grind(&mut self,bits:usize)->F {
        if bits==0 {return F::ZERO;}
        // A single BabyBear witness has < 2^31 values; z >= 29 would need a wider witness.
        assert!(bits<=28,"grinding above 28 bits needs a multi-element witness (not implemented)");
        use openvm_stark_backend::p3_maybe_rayon::prelude::*;
        self.flush();
        let start=std::time::Instant::now();
        let base=self.clone();
        COUNT_GRIND.store(false,std::sync::atomic::Ordering::Relaxed);
        // Deterministic: the smallest valid witness, searched in parallel chunks of 2^16.
        const CH:u32=1<<16;
        let mut w=None;
        for chunk in 0..(2013265921u32/CH) {
            let lo=chunk*CH;
            w=(lo..lo+CH).into_par_iter().find_first(|&w|base.pow_step(w,bits).1);
            if w.is_some() {break;}
        }
        let w=w.expect("no PoW witness");
        COUNT_GRIND.store(true,std::sync::atomic::Ordering::Relaxed);
        GRIND_STATS.lock().unwrap().push((bits,start.elapsed().as_secs_f64(),w as u64));
        let witness=F::from_u32(w);
        assert!(self.check_witness(bits,witness));
        witness
    }
}
struct Engine {device:ReferenceDevice<SC>}
impl StarkEngine for Engine {
    type SC=SC;type PB=CpuColMajorBackend<SC>;type PD=ReferenceDevice<SC>;type TS=Transcript;
    fn new(params:SystemParams)->Self {Self {device:ReferenceDevice::new(SC{params,hasher:ShaHasher})}}
    fn config(&self)->&SC {self.device.config()}
    fn device(&self)->&Self::PD {&self.device}
    fn initial_transcript(&self)->Transcript {Transcript::new()}
    fn prover_from_transcript(&self,t:Transcript)->Coordinator<SC,Self::PB,Self::PD,Transcript> {
        Coordinator::new(CpuColMajorBackend::new(),self.device.clone(),t)
    }
}
fn transcript_vectors() {
    let hasher=ShaHasher;
    let leaf=hasher.hash_slice(&[F::ZERO,F::ONE,F::from_u32(2013265920)]);
    let empty=hasher.hash_slice(&[]);
    let node=hasher.compress(leaf,empty);
    let mut t=Transcript::new();for n in [123,124,0,2013265920] {t.observe(F::from_u32(n));} t.observe_commit(node);
    let samples:Vec<u32>=(0..96).map(|i| {
        if i>=32 && (i-32)%7==0 {t.observe(F::from_u32(i));t.observe(F::from_u32(i+1));}
        t.sample().as_canonical_u32()
    }).collect();
    println!("VECTOR_LEAF {:?}",digest_wire(leaf));
    println!("VECTOR_EMPTY {:?}",digest_wire(empty));
    println!("VECTOR_NODE {:?}",digest_wire(node));
    println!("VECTOR_SAMPLES {:?}",samples);
    println!("VECTOR_STATE {:?}",t.state.to_vec());
    println!("VECTOR_CURSOR {}",t.next_word);
    if levers().coset_leaf {
        let coset=hasher.hash_coset(&[vec![F::ZERO,F::ONE],vec![F::from_u32(2),F::from_u32(2013265920)]]);
        println!("VECTOR_COSET {:?}",digest_wire(coset));
    }
}
