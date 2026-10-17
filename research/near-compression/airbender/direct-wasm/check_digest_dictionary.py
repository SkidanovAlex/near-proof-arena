"""Self-contained digest deduplication; exact proof reconstruction and native replay."""
from collections import Counter
import hashlib,json,os,struct,subprocess,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'results/native-literal-sha384-ext12-compact'
OUT=ROOT/'results/native-literal-digest-dictionary';OUT.mkdir(exist_ok=True)
raw=(SOURCE/'child.proof').read_bytes()
auth=(SOURCE/'auth-digests.bin').read_bytes();assert len(auth)%48==0
counts=Counter(auth[i:i+48] for i in range(0,len(auth),48))
dictionary=sorted(d for d,n in counts.items() if n>=2)
assert len(dictionary)<=65536
lookup={d:i for i,d in enumerate(dictionary)}
wire=bytearray(b'NPDICT01'+struct.pack('<II',len(raw),len(dictionary))+b''.join(dictionary))
literal=bytearray();refs=0;i=0
while i<len(raw):
    index=lookup.get(raw[i:i+48])
    if index is None:literal.append(raw[i]);i+=1;continue
    if literal:wire+=b'\0'+struct.pack('<I',len(literal))+literal;literal.clear()
    wire+=b'\1'+struct.pack('<H',index);i+=48;refs+=1
if literal:wire+=b'\0'+struct.pack('<I',len(literal))+literal
wire=bytes(wire)
def decode(w):
    assert w[:8]==b'NPDICT01';size,n=struct.unpack_from('<II',w,8)
    assert size<=16*1024*1024 and n<=65536
    pos=16+n*48;assert pos<=len(w)
    dictionary=[w[16+48*i:64+48*i] for i in range(n)];out=bytearray()
    while pos<len(w):
        tag=w[pos];pos+=1
        if tag==0:
            count=struct.unpack_from('<I',w,pos)[0];pos+=4
            assert count>0 and pos+count<=len(w);block=w[pos:pos+count];pos+=count
        else:
            assert tag==1;idx=struct.unpack_from('<H',w,pos)[0];pos+=2
            assert idx<n;block=dictionary[idx]
        assert len(out)+len(block)<=size;out+=block
    assert len(out)==size;return bytes(out)
assert decode(wire)==raw
(OUT/'child.dictionary').write_bytes(wire)
# Isolated Rust binary verifies dictionary output without the original proof,
# traces or fixture. Retain only expected public statement at this path.
shutil.copyfile(SOURCE/'public.bin',OUT/'public.bin')
env=dict(os.environ,NEARPROOF_REPLAY='1',NEARPROOF_DICTIONARY=str(OUT/'child.dictionary'),
         NEARPROOF_LITERAL_OUT=str(OUT),NEARPROOF_QUERY_BITS='268',RAYON_NUM_THREADS='4')
for name in ['NEARPROOF_TRANSCRIPT_VECTORS','NEARPROOF_WHIR_CENSUS']:env.pop(name,None)
command=['cargo','run','--locked','--manifest-path','/tmp/nearproof-native-sha384/Cargo.toml','--release']
result=subprocess.run(command,env=env,text=True,capture_output=True,check=True)
assert 'NATIVE_SHA384_EXT12_REPLAY_PASS' in result.stdout
(OUT/'replay.log').write_text(result.stdout+result.stderr)
# Change a live dictionary entry. Native cryptographic verification must reject;
# successful structural decompression alone is not acceptance.
bad=bytearray(wire);bad[16]^=1
assert decode(bad)!=raw
(OUT/'mutated.dictionary').write_bytes(bad)
env['NEARPROOF_DICTIONARY']=str(OUT/'mutated.dictionary')
negative=subprocess.run(command,env=env,text=True,capture_output=True)
assert negative.returncode!=0 and 'NATIVE_DICTIONARY_DECODE' in negative.stdout
assert 'NATIVE_SHA384_EXT12_REPLAY_PASS' not in negative.stdout
assert 'WhirError(MerkleVerify)' in negative.stderr
(OUT/'mutation.log').write_text(negative.stdout+negative.stderr)
(OUT/'mutated.dictionary').unlink()
# Independently exercise the Rust decoder's failure paths using a tiny test
# runner compiled from the very same source used by the native proof verifier.
source=Path(__file__).with_name('native_digest_dictionary.rs').read_text()
tests=source+'''\nfn main(){
 let valid=std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
 assert!(decode_digest_dictionary(&valid).is_ok());
 for n in [0,7,15,valid.len()-1] {assert!(decode_digest_dictionary(&valid[..n]).is_err());}
 let mut bad=valid.clone();bad.extend([255]);assert!(decode_digest_dictionary(&bad).is_err());
 let mut bad=valid.clone();bad[8..12].copy_from_slice(&u32::MAX.to_le_bytes());assert!(decode_digest_dictionary(&bad).is_err());
 let mut bad=valid.clone();bad[12..16].copy_from_slice(&65537u32.to_le_bytes());assert!(decode_digest_dictionary(&bad).is_err());
 let invalid_ref=[b"NPDICT01".as_slice(),&48u32.to_le_bytes(),&0u32.to_le_bytes(),&[1,0,0]].concat();
 assert!(decode_digest_dictionary(&invalid_ref).is_err());
 println!("DICTIONARY_MALFORMED_PASS cases=8");
}\n'''
Path('/tmp/nearproof-dictionary-tests.rs').write_text(tests)
subprocess.run(['rustc','--edition=2024','/tmp/nearproof-dictionary-tests.rs','-o','/tmp/nearproof-dictionary-tests'],check=True)
test=subprocess.run(['/tmp/nearproof-dictionary-tests',str(OUT/'child.dictionary')],text=True,capture_output=True,check=True)
(OUT/'malformed.log').write_text(test.stdout+test.stderr)
for name in ['main.rs','native_sha384_config.rs','literal.rs']:
    shutil.copyfile('/tmp/nearproof-native-sha384/src/'+name,OUT/name)
for name in ['Cargo.toml','Cargo.lock']:
    shutil.copyfile('/tmp/nearproof-native-sha384/'+name,OUT/name)
(OUT/'native_digest_dictionary.rs').write_text(source)
shutil.copyfile('/tmp/nearproof-whir-census.log',OUT/'whir-census.log')
shutil.copyfile(SOURCE/'auth-digests.bin',OUT/'auth-digests.bin')
report=dict(status='LOSSLESS_DICTIONARY_NATIVE_REPLAY_VERIFIED',native_bytes=len(raw),wire_bytes=len(wire),
    total_wire_plus_request_bytes=len(wire)+919,bytes_saved=len(raw)-len(wire),dictionary_entries=len(dictionary),references=refs,
    native_sha256=hashlib.sha256(raw).hexdigest(),wire_sha256=hashlib.sha256(wire).hexdigest(),
    exact_python_roundtrip=True,independent_rust_native_replay=True,dictionary_payload_mutation_rejected=True,
    malformed_cases=8,security_certified=False,
    scope='Transport encoding only; dictionary included. Same native verifier and cryptographic parameters. No recursive proof or new quantum-security claim.')
report['sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file() and p.name!='report.json'}
(OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
