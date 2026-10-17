"""Check actual Ext12/SHA384 Wasm proof, independent transcript and Lean oracle."""
import hashlib,json,os,re,shutil,struct,subprocess,tempfile,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser();ap.add_argument('--input-source',type=Path,default=ROOT/'results/native-literal-field-screen');ap.add_argument('--out',type=Path,default=ROOT/'results/native-literal-sha384-ext12-compact');ap.add_argument('--prove-log',type=Path,default=Path('/tmp/nearproof-native-sha384.log'));args=ap.parse_args()
OUT=args.out.resolve()
TMP=Path('/tmp/nearproof-native-sha384')
BACKEND=Path('/home/illia/.cargo/git/checkouts/stark-backend-708f1155344bec0c/d667af5')
log=args.prove_log.read_text()
profile=re.search(r'NATIVE_SHA384_PROFILE n_stack=(\d+) k=(\d+) log_blowup=(\d+) (?:all_list=(\d+) )?queries=(\[[^\n]+\])',log)
params=(dict(n_stack=int(profile[1]),k=int(profile[2]),log_blowup=int(profile[3]),all_list=int(profile[4] or 0),queries=json.loads(profile[5])) if profile else dict(n_stack=16,k=3,log_blowup=5,all_list=0,queries=None))
interaction_match=re.search(r'NATIVE_SHA384_INTERACTION_LOG (\d+)',log)
params['interaction_log']=int(interaction_match[1]) if interaction_match else 20
assert 'NATIVE_SHA384_EXT12_PASS public_mutations_rejected=6' in log
m=re.search(r'NATIVE_SHA384_EXT12_BYTES total=(\d+) gkr=(\d+) relations=(\d+) stacking=(\d+) whir=(\d+)',log)
assert m
census=dict(zip(['total','gkr','relations','stacking','whir'],map(int,m.groups())))
census['other']=census['total']-sum(v for k,v in census.items() if k!='total')
assert census['total']==(OUT/'child.proof').stat().st_size and census['other']>=0
bound=re.search(r'NATIVE_SHA384_EXT12 target=(\d+) min=([^ ]+) logup=([^ ]+) proximity=([^ ]+) query=([^\n]+)',log)
assert bound and int(bound[1])==268
(OUT/'prove.log').write_text(log)
# A separate SHA384 implementation (Python/OpenSSL) and separately written
# framing/sampler reproduce all transcript states, including rejection steps.
vector_log=Path('/tmp/nearproof-native-sha384-vectors.log').read_text()
vectors={line.split(' ',1)[0]:json.loads(line.split(' ',1)[1]) for line in vector_log.splitlines() if line.startswith('VECTOR_')}
def h(tag,*parts):
    framed=b'nearproof-native-sha384-ext12-v4'+bytes([tag])
    for p in parts:framed+=len(p).to_bytes(8,'little')+p
    return hashlib.sha384(framed).digest()
def word(n):return n.to_bytes(4,'little')
leaf=h(0,word(0)+word(1)+word(2013265920));empty=h(0,b'');node=hashlib.sha384(b'NPQ4NODE'+leaf+empty).digest()
assert vectors['VECTOR_LEAF']==list(leaf) and vectors['VECTOR_EMPTY']==list(empty) and vectors['VECTOR_NODE']==list(node)
state=h(2);state=h(3,state,b''.join(word(n) for n in [123,124,0,2013265920]));state=h(4,state,node)
samples=[];rejections=0;cursor=12;draw_blocks=0
for i in range(96):
    if i>=32 and (i-32)%7==0:state=h(3,state,word(i)+word(i+1));cursor=12
    while True:
        if cursor==12:state=h(5,state);cursor=0;draw_blocks+=1
        n=int.from_bytes(state[cursor*4:cursor*4+4],'little');cursor+=1
        if n<4026531842:samples.append(n%2013265921);break
        rejections+=1
assert rejections>0 and vectors['VECTOR_SAMPLES']==samples and vectors['VECTOR_STATE']==list(state) and vectors['VECTOR_CURSOR']==cursor
(OUT/'transcript-vectors.log').write_text(vector_log)
# Reconstruct only fixed key and expected statement; no trace or fixture access.
env=dict(os.environ,NEARPROOF_LITERAL_OUT=str(OUT),NEARPROOF_REPLAY='1',NEARPROOF_QUERY_BITS='268',RAYON_NUM_THREADS='4')
env.pop('NEARPROOF_TRANSCRIPT_VECTORS',None)
env.pop('NEARPROOF_DICTIONARY',None)
env.pop('NEARPROOF_WHIR_CENSUS',None)
env.update(NEARPROOF_N_STACK=str(params['n_stack']),NEARPROOF_K=str(params['k']),NEARPROOF_LOG_BLOWUP=str(params['log_blowup']),NEARPROOF_ALL_LIST=str(params['all_list']),NEARPROOF_INTERACTION_LOG=str(params['interaction_log']))
moved=[]
try:
    for name in [p.name for p in sorted(OUT.glob('rows-*.bin'))]+['fixture.json','spec.json']:
        p=OUT/name;q=OUT/(name+'.hidden');assert not q.exists();p.rename(q);moved.append((p,q))
    replay=subprocess.run(['cargo','run','--locked','--manifest-path',str(TMP/'Cargo.toml'),'--release'],env=env,text=True,capture_output=True,check=True)
    assert 'NATIVE_SHA384_EXT12_REPLAY_PASS' in replay.stdout
    (OUT/'replay.log').write_text(replay.stdout+replay.stderr)
finally:
    for p,q in reversed(moved):q.rename(p)
public=[x[0] for x in struct.iter_unpack('<I',(OUT/'public.bin').read_bytes())]
request=ROOT/'results/pq384-code-table-long193/request.json'
with tempfile.TemporaryDirectory() as tmp:
    inp=Path(tmp)/'input.json';inp.write_text(json.dumps(dict(request=json.loads(request.read_text()),public=public)))
    eligibility=subprocess.run(['lake','env','lean','--run','PreparedSliceCheck.lean',str(inp)],cwd=ROOT,text=True,capture_output=True,check=True)
    assert json.loads(eligibility.stdout)==dict(status='PASS',code_length=193)
    oracle=subprocess.run(['lake','env','lean','--run','PreparedSliceOracle.lean',str(request),'256'],cwd=ROOT,text=True,capture_output=True,check=True)
actual=json.loads(oracle.stdout)
verify_calls=json.loads(re.search(r'NATIVE_SHA384_VERIFY_CALLS (\[[^\n]+\])',replay.stdout)[1])
verify_blocks=json.loads(re.search(r'NATIVE_SHA384_VERIFY_BLOCKS (\[[^\n]+\])',replay.stdout)[1])
claimed=dict(done=public[44]==1,failed=public[45]==1,gas=sum(public[46+i]<<(16*i) for i in range(4)),stack=[public[50+2*i]+(public[51+2*i]<<16) for i in range(public[43])])
assert actual==claimed
for name in ['public.bin','spec.json','fixture.json']+[p.name for p in sorted(args.input_source.glob('rows-*.bin'))]:
    assert (OUT/name).read_bytes()==(args.input_source/name).read_bytes()
assert (OUT/'public.bin').read_bytes()==(ROOT/'results/native-literal-field-screen/public.bin').read_bytes()
for name in ['main.rs','native_sha384_config.rs','native_digest_dictionary.rs','literal.rs']:shutil.copyfile(TMP/'src'/name,OUT/name)
for name in ['Cargo.toml','Cargo.lock']:shutil.copyfile(TMP/name,OUT/name)
(OUT/'backend.patch').write_bytes(subprocess.check_output(['git','diff','--','crates/stark-backend'],cwd=BACKEND))
shutil.copyfile(ROOT/'results/babybear-ext12-construction/plonky3-ext12.patch',OUT/'plonky3-ext12.patch')
packing=json.loads((OUT/'packing.json').read_text()) if (OUT/'packing.json').exists() else None
report=dict(packing=packing,input_source=str(args.input_source),status='NATIVE_WASM_CHILD_SHA384_EXT12_VERIFIED',child_bytes=census['total'],wire_census=census,
    public_fields=4891,public_included=True,request_bytes=request.stat().st_size,total_child_plus_request_bytes=census['total']+request.stat().st_size,
    independent_Lean_runCall=actual,eligibility=json.loads(eligibility.stdout),public_mutations_rejected=6,
    witness_independent_replay=True,transcript_oracle=dict(samples=96,rejections=rejections,draw_blocks=draw_blocks,final_state_equal=True,version=4),
    verifier_hash_cost=dict(tags=['leaf','node','init','observe_field','observe_commit','draw_block'],calls=verify_calls,compression_blocks=verify_blocks,total_compression_blocks=sum(verify_blocks),scope='single engine.verify call; excludes keygen and decoding'),
    security=dict(hash='SHA-384',field='BabyBear[X]/(X^12-31)',query_target_bits=268,grinding_bits=0,parameters=params,
        native_component_min_bits=float(bound[2]),logup_bits=float(bound[3]),proximity_bits=float(bound[4]),query_bits=float(bound[5]),certified=False),
    backend_pin=subprocess.check_output(['git','rev-parse','HEAD'],cwd=BACKEND,text=True).strip(),
    exclusions=['custom transcript compiler/QROM applicability and concrete constants',
        'recursive parent upgrade and knowledge composition','Lean field irreducibility and Rust refinement',
        'packed AIR-to-original AIR refinement' if packing else 'native AIR implementation refinement','cryptographic acceptance-to-execution Lean theorem','full NEAR1Pgas and performance target'],
    sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file() and p.name!='report.json'})
(OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
