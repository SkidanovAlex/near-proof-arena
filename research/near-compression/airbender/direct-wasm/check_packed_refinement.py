"""Integrated executable evidence for the structural HoldsP transfer premises.
The universal theorem is kernel-checked; a closed concrete certificate is pending.
"""
import concurrent.futures,hashlib,json,subprocess
from pathlib import Path
import prepared_code_table_air as lit
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
source=ROOT/'results/native-literal-byte-packed-input'
old,_=lit.make(json.loads((source/'fixture.json').read_text()))
packed=json.loads((source/'spec.json').read_text())
a,b=old['air'],packed['air']
assert len(a['tables'])==2 and len(b['tables'])==3
assert a['pubSegs']==b['pubSegs'] and a['maxPub']==b['maxPub']
assert old['public']==packed['public']
assert all(b['tables'][i]['maxLog']<=a['tables'][i]['maxLog'] for i in range(2))
checks=['macros','layout','rewrite','range','constraints','bus']
def run(name):
    process=subprocess.run(['python3',str(HERE/f'check_packed_{name}.py')],cwd=ROOT,text=True,capture_output=True)
    if process.returncode:raise RuntimeError(f'{name}: {process.stdout}\n{process.stderr}')
    result=json.loads(process.stdout);assert result['status']=='PASS'
    return name,result
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    reports=dict(pool.map(run,checks))
print(json.dumps(dict(status='PASS',universal_theorem='NearCompression.packed_holds_refinement',
    concrete_closed_kernel_certificate=False,native_acceptance_to_HoldsP=False,
    structural_metadata=dict(original_tables=2,packed_tables=3,public_segments_equal=True,
        public_maximum_equal=True,max_log_not_increased=True,public_values_equal=True),
    checks=reports,source_spec_sha256=hashlib.sha256((source/'spec.json').read_bytes()).hexdigest(),
    scope='All current structural artifact checks pass for the conditional universal HoldsP theorem. This is executable evidence, not a closed kernel proof for the concrete full AIR or cryptographic soundness.'),indent=2))
