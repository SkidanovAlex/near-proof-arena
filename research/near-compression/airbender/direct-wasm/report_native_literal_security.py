"""Reconcile measured integrated proofs and actual-key component estimates."""
import sys as _sys;from pathlib import Path as _P;_sys.path.insert(0,str(_P(__file__).resolve().parents[2]/'native'));import native_paths
import hashlib,json,re,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/native-literal-security-comparison';OUT.mkdir(exist_ok=True)
rows=[]
for rate,suffix in [(1,''),(3,'-rate3'),(5,'-rate5')]:
 p=ROOT/'results'/('native-literal-query128'+suffix)
 r=json.loads((p/'report.json').read_text())
 assert r['security']['whir_query_target_bits']==128 and not r['security']['PQ128']
 assert all(x['grinding_bits']==0 and x['log_blowup']==rate for x in r['security']['profiles'])
 for name in ['child.proof','parent.proof']:
  assert hashlib.sha256((p/name).read_bytes()).hexdigest()==r['sha256'][name]
  assert (p/name).stat().st_size==r[name.split('.')[0]+'_bytes']
 assert r['fresh_replay_without']==['child proof','source rows','fixture','spec']
 assert r['parent_public_mutation_rejections']==6
 c=r['parent_wire_census'];assert c['total']==sum(v for k,v in c.items() if k!='total')
 parent=next(b for b in r['native_vk_component_estimates'] if b['stage']=='parent')
 duration=float(re.search(r'finished in ([0-9.]+)s', (p/'prove.log').read_text().split('test result: ok.')[-1])[1])
 rows.append(dict(log_blowup=rate,child_bytes=r['child_bytes'],parent_bytes=r['parent_bytes'],
  total_parent_plus_request=r['total_parent_plus_request_bytes'],test_seconds_excluding_build=duration,
  whir_bytes=c['whir'],whir_fraction=c['whir']/c['total'],native_parent_min_component_bits=parent['min_component'],
  native_parent_query_bits=parent['query'],native_parent_proximity_bits=parent['proximity'],
  strict_300000_byte_gate=r['total_parent_plus_request_bytes']<300000,
  PQ128_certified=False,report_sha256=hashlib.sha256((p/'report.json').read_bytes()).hexdigest()))
backend=native_paths.BACKEND
sources={}
for rel in ['crates/stark-backend/src/config.rs','crates/stark-backend/src/soundness/calculator.rs','crates/stark-backend/src/soundness/vk.rs']:
 dst=OUT/(rel.replace('/','__')+'.txt');shutil.copyfile(backend/rel,dst)
 sources[rel]=hashlib.sha256(dst.read_bytes()).hexdigest()
report=dict(rows=rows,source_hashes=sources,
 decision='Stop query-only tuning of this fixed Ext4 profile. The integrated parent misses size and the current native component bounds do not support 128 bits, before QROM/composition.',
 scope='Finite measured configurations, not an impossibility theorem. Native calculator minima are conservative component/RBR estimates, not end-to-end security guarantees.',
 next_gate='Choose field/hash/proximity parameters with a complete quantum soundness ledger for this same integrated slice before further size optimization; preserve public statement binding and source semantics.')
(OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
