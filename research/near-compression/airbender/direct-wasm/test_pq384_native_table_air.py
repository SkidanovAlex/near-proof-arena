import argparse,json,sys
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True)
p.add_argument('--fixture',required=True);p.add_argument('--folded-library',required=True)
a=p.parse_args();sys.path.append(a.reference_dir)
import pq384_table_air as air
from pq384_native_table_air import prove_native
f=json.loads(Path(a.fixture).read_text());spec={k:f[k] for k in ('air','table_index','public')}
spec.update(log_rows=3,packing=16)
root=air.source_commitment(f['rows'],spec)
reference=air.prove(spec,root,f['rows'])
actual,timing=prove_native(spec,root,f['rows'],folded_library=a.folded_library)
assert actual==reference
assert air.verify_table_local(actual,spec,root)
print(json.dumps(dict(status='PASS',exact_full_proof_parity=True,timing=timing)))
