"""Archive native Wasm child/parent evidence; replay without child or trace files."""
import hashlib,json,os,shutil,struct,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/native-literal-recursion'
OPENVM=Path('/tmp/nearproof-openvm')
BACKEND=Path('/home/illia/.cargo/git/checkouts/stark-backend-708f1155344bec0c/d667af5')
command=['cargo','test','--locked','--profile','fast','-p','openvm-recursion-circuit',
         'tests::native_literal::nearproof_literal_slice_recursion','--','--exact','--nocapture']
log=Path('/tmp/nearproof-native-literal-bound.log').read_text()
assert 'NEARPROOF_LITERAL_PARENT_BYTES=97689 PUBLIC_FIELDS=4891 NEGATIVES=6' in log
assert 'test result: ok. 1 passed' in log
(OUT/'prove.log').write_text(log)
env=dict(os.environ,RAYON_NUM_THREADS='4',NEARPROOF_LITERAL_OUT=str(OUT),NEARPROOF_LITERAL_REPLAY='1')
moved=[]
try:
 for name in ['rows-0.bin','rows-1.bin','child.proof','fixture.json','spec.json']:
  p=OUT/name;q=OUT/(name+'.hidden');assert not q.exists();p.rename(q);moved.append((p,q))
 result=subprocess.run(command,cwd=OPENVM,env=env,text=True,capture_output=True,check=True)
 assert 'NEARPROOF_LITERAL_REPLAY_PASS' in result.stdout
 (OUT/'replay.log').write_text(result.stdout+result.stderr)
finally:
 for p,q in reversed(moved):q.rename(p)
request=ROOT/'results/pq384-code-table-long193/request.json'
public=[x[0] for x in struct.iter_unpack('<I',(OUT/'public.bin').read_bytes())]
with tempfile.TemporaryDirectory() as tmp:
 inp=Path(tmp)/'input.json';inp.write_text(json.dumps(dict(request=json.loads(request.read_text()),public=public)))
 eligibility=subprocess.run(['lake','env','lean','--run','PreparedSliceCheck.lean',str(inp)],cwd=ROOT,text=True,capture_output=True,check=True)
 assert json.loads(eligibility.stdout)==dict(status='PASS',code_length=193)
 oracle=subprocess.run(['lake','env','lean','--run','PreparedSliceOracle.lean',str(request),'256'],cwd=ROOT,text=True,capture_output=True,check=True)
actual=json.loads(oracle.stdout)
claimed=dict(done=public[44]==1,failed=public[45]==1,gas=sum(public[46+i]<<(16*i) for i in range(4)),stack=[public[50+2*i]+(public[51+2*i]<<16) for i in range(public[43])])
assert actual==claimed
patch=subprocess.check_output(['git','diff','--','crates/stark-backend/src/keygen/types.rs','crates/stark-backend/src/interaction/debug.rs'],cwd=BACKEND)
(OUT/'backend.patch').write_bytes(patch)
(OUT/'openvm-hook.patch').write_text('diff --git a/crates/recursion/src/tests.rs b/crates/recursion/src/tests.rs\n--- a/crates/recursion/src/tests.rs\n+++ b/crates/recursion/src/tests.rs\n@@ -1,0 +1,2 @@\n+#[path = "native_literal.rs"]\n+mod native_literal;\n')
report=dict(status='NATIVE_LITERAL_CHILD_AND_BOUND_PARENT_VERIFIED',child_bytes=(OUT/'child.proof').stat().st_size,parent_bytes=(OUT/'parent.proof').stat().st_size,
 public_fields=4891,public_fields_are_inside_parent_serialization=True,request_bytes=request.stat().st_size,
 total_parent_plus_request_bytes=(OUT/'parent.proof').stat().st_size+request.stat().st_size,
 fresh_replay_without=['child proof','source rows','fixture','spec'],parent_public_mutation_rejections=6,
 independent_runCall=actual,eligibility=json.loads(eligibility.stdout),
 security=dict(whir_test_security_bits=5,field='BabyBear Ext4',hash='Poseidon2',PQ128=False),
 modifications=['Exact original AIR expression DAG and bus messages lowered to native builder.',
 'CODE multiplicity high bits >=9 constrained zero (511 bound, 256 actual execution rows).',
 'Twelve public count bytes fixed to [1,0,0,0,1,0,0,0,193,0,0,0].',
 'Parent continuation public-value bus consumed by public binding AIR; prehash bus consumed.',
 'Scaled trace-height implication gate and selector-aware debug evaluator.'],
 limits=['Five-bit WHIR test setting: sizes do not establish secure compression.',
 'No compiler refinement or cryptographic acceptance-to-HoldsP Lean theorem.',
 'No adversarial-witness proving test yet.',
 'Bounded i32 Wasm slice only; no full NEAR1Pgas.'],
 pins={str(p):subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip() for p in [OPENVM,BACKEND]})
report['sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.iterdir() if p.is_file() and p.name!='report.json'}
(OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
