"""Archive native Wasm child/parent evidence; replay without child or trace files."""
import sys as _sys;from pathlib import Path as _P;_sys.path.insert(0,str(_P(__file__).resolve().parents[2]/'native'));import native_paths
import argparse,hashlib,json,math,os,re,struct,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out',type=Path,default=ROOT/'results/native-literal-recursion')
parser.add_argument('--prove-log',type=Path,default=Path('/tmp/nearproof-native-literal-bound.log'))
parser.add_argument('--query-bits',type=int)
parser.add_argument('--log-blowup',type=int)
args=parser.parse_args()
OUT=args.out.resolve()
OPENVM=Path('/tmp/nearproof-openvm')
BACKEND=native_paths.BACKEND
command=['cargo','test','--locked','--profile','fast','-p','openvm-recursion-circuit',
         'tests::native_literal::nearproof_literal_slice_recursion','--','--exact','--nocapture']
log=args.prove_log.read_text()
size_match=re.search(r'NEARPROOF_LITERAL_PARENT_BYTES=(\d+) PUBLIC_FIELDS=4891 NEGATIVES=6',log)
assert size_match and int(size_match[1])==(OUT/'parent.proof').stat().st_size
assert 'test result: ok. 1 passed' in log
(OUT/'prove.log').write_text(log)
env=dict(os.environ,RAYON_NUM_THREADS='4',NEARPROOF_LITERAL_OUT=str(OUT),NEARPROOF_LITERAL_REPLAY='1')
env.pop('NEARPROOF_LITERAL_QUERY_BITS',None)
env.pop('NEARPROOF_LITERAL_LOG_BLOWUP',None)
if args.log_blowup is not None:
 assert args.query_bits is not None
 env['NEARPROOF_LITERAL_LOG_BLOWUP']=str(args.log_blowup)
profiles=[]
if args.query_bits is not None:
 env['NEARPROOF_LITERAL_QUERY_BITS']=str(args.query_bits)
 for stage in ['child','parent']:
  match=re.search(rf'NEARPROOF_LITERAL_QUERY_PROFILE stage={stage} query_bits=(\d+) log_blowup=(\d+) queries=(\[[^\n]+?\]) pow=0 field=Ext4 hash=Poseidon2',log)
  assert match and int(match[1])==args.query_bits
  assert int(match[2])==(args.log_blowup if args.log_blowup is not None else 1)
  profiles.append(dict(stage=stage,query_bits=int(match[1]),log_blowup=int(match[2]),queries=json.loads(match[3]),grinding_bits=0))
moved=[]
try:
 for name in ['rows-0.bin','rows-1.bin','child.proof','fixture.json','spec.json']:
  p=OUT/name;q=OUT/(name+'.hidden');assert not q.exists();p.rename(q);moved.append((p,q))
 result=subprocess.run(command,cwd=OPENVM,env=env,text=True,capture_output=True,check=True)
 assert 'NEARPROOF_LITERAL_REPLAY_PASS' in result.stdout
 (OUT/'replay.log').write_text(result.stdout+result.stderr)
finally:
 for p,q in reversed(moved):q.rename(p)
(OUT/'replay-source.rs.txt').write_bytes((OPENVM/'crates/recursion/src/native_literal.rs').read_bytes())
census_match=re.search(r'NEARPROOF_LITERAL_CENSUS stage=parent total=(\d+) gkr=(\d+) relations=(\d+) stacking=(\d+) whir=(\d+) other=(\d+)',result.stdout)
census=None
if census_match:
 census=dict(zip(['total','gkr','relations','stacking','whir','other'],map(int,census_match.groups())))
 assert census['total']==sum(v for k,v in census.items() if k!='total')==(OUT/'parent.proof').stat().st_size
rbr=[]
for match in re.finditer(r'NEARPROOF_LITERAL_RBR stage=(child|parent) ([^\n]+)',result.stdout):
 rbr.append(dict(stage=match[1],**{k:float(v) for k,v in (part.split('=') for part in match[2].split())}))
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
 parent_wire_census=census,
 independent_runCall=actual,eligibility=json.loads(eligibility.stdout),
 security=dict(whir_query_target_bits=args.query_bits if args.query_bits is not None else 5,
 profiles=profiles,field='BabyBear Ext4',field_cardinality_bits=4*math.log2(2013265921),hash='Poseidon2',PQ128=False),
 native_vk_component_estimates=rbr,
 native_estimate_scope='Upstream conservative component/RBR calculator; its minimum is not a composed Fiat-Shamir/QROM security certificate.',
 modifications=['Exact original AIR expression DAG and bus messages lowered to native builder.',
 'CODE multiplicity high bits >=9 constrained zero (511 bound, 256 actual execution rows).',
 'Twelve public count bytes fixed to [1,0,0,0,1,0,0,0,193,0,0,0].',
 'Parent continuation public-value bus consumed by public binding AIR; prehash bus consumed.',
 'Scaled trace-height implication gate and selector-aware debug evaluator.'],
 limits=['WHIR query target alone does not establish whole-protocol or PQ security; field and hash unchanged.',
 'No compiler refinement or cryptographic acceptance-to-HoldsP Lean theorem.',
 'No adversarial-witness proving test yet.',
 'Bounded i32 Wasm slice only; no full NEAR1Pgas.'],
 pins={str(p):subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip() for p in [OPENVM,BACKEND]})
report['sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.iterdir() if p.is_file() and p.name!='report.json'}
(OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
