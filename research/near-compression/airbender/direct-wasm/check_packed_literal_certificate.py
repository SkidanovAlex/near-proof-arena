"""Build/audit the closed certificate and compare its AIR to saved proving input."""
import hashlib,json,subprocess
from pathlib import Path
import prepared_code_table_air as lit
ROOT=Path(__file__).resolve().parents[2]
source=ROOT/'results/native-literal-byte-packed-input'
out=ROOT/'results/native-literal-byte-packed'
def run(args):
    p=subprocess.run(args,cwd=ROOT,text=True,capture_output=True)
    if p.returncode:raise RuntimeError(p.stdout+'\n'+p.stderr)
    return p
build=run(['lake','build','NearCompression.PackedLiteralExecution'])
(out/'closed-certificate-build.log').write_text(build.stdout+build.stderr)
audit=run(['lake','env','lean','PackedLiteralAudit.lean'])
assert 'sorryAx' not in audit.stdout and 'Lean.ofReduceBool' not in audit.stdout
assert len(audit.stdout.strip().splitlines())==4
(out/'lean-closed-certificate-audit.log').write_text(audit.stdout)
export=run(['lake','env','lean','--run','PackedLiteralExport.lean'])
actual=json.loads(export.stdout)
old,_=lit.make(json.loads((source/'fixture.json').read_text()))
packed=json.loads((source/'spec.json').read_text())
assert actual==[old['air'],packed['air']]
report=dict(status='PASS',concrete_closed_kernel_certificate=True,
    theorems=['packed_original_literal_eq','packed_literal_holds','packed_literal_public_run_call'],
    exported_air_equals_proving_input=True,source_constraints=sum(len(t['constraints']) for t in old['air']['tables']),
    packed_air_sha256=hashlib.sha256((source/'spec.json').read_bytes()).hexdigest(),
    native_acceptance_to_HoldsP=False,quantum_security_certified=False,full_NEAR=False,
    scope='Closed semantic AIR-to-runCall theorem for the supported prepared literal slice. Native Rust/compiler refinement, cryptographic acceptance, QROM recursion and full NEAR remain open.')
print(json.dumps(report,indent=2))
