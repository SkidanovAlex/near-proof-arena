"""Cross-layer binding tests using a retained real 193-instruction proof."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from verify_prepared_slice import PACKAGE, verify


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fixture', type=Path, default=PACKAGE / 'results/pq384-code-table-long193')
    parser.add_argument('--gkr', action='store_true')
    args = parser.parse_args()
    fixture = args.fixture
    if args.gkr:
        from verify_prepared_gkr_slice import verify
        frontend = 'verify_prepared_gkr_slice.py'
    else:
        from verify_prepared_slice import verify
        frontend = 'verify_prepared_slice.py'
    wire = (fixture / 'proof.bin').read_bytes()
    statement = json.loads((fixture / 'statement.json').read_text())
    request = json.loads((fixture / 'request.json').read_text())
    fresh = subprocess.run([sys.executable, str(Path(__file__).with_name(frontend)),
                            str(fixture / 'proof.bin'), str(fixture / 'statement.json'),
                            str(fixture / 'request.json')], check=True, capture_output=True, text=True)
    assert json.loads(fresh.stdout)['status'] == 'PASS'
    rejected = []

    def reject(label, mutate, stage):
        st, req = copy.deepcopy(statement), copy.deepcopy(request)
        changed = mutate(st, req)
        try:
            verify(wire if changed is None else changed, st, req)
        except subprocess.CalledProcessError as exc:
            if stage != 'preparation' or 'literal runCall eligibility rejected' not in exc.stderr + exc.stdout:
                raise
        except (ValueError, AssertionError) as exc:
            if stage == 'preparation':
                raise AssertionError('expected actual Lean eligibility rejection') from exc
        else:
            raise AssertionError(label + ' accepted')
        rejected.append(dict(case=label, stage=stage))

    reject('different requested method', lambda s,r:r.update(method='missing'), 'preparation')
    reject('different prepaid gas', lambda s,r:r.update(prepaid=r['prepaid']-1), 'preparation')
    # Change a valid i32.const immediate in the requested program, preserving its encoding.
    def other_program(s, r):
        code = r['wasm_bytes']
        pos = next(i for i in range(len(code)-2, -1, -1) if code[i:i+2] == [0x41, 1])
        code[pos+1] = 2
    reject('different valid requested Wasm program', other_program, 'preparation')
    reject('noncanonical Wasm byte', lambda s,r:r['wasm_bytes'].__setitem__(0,256), 'frontend')
    reject('prover-selected AIR', lambda s,r:s['spec']['air']['tables'][0]['constraints'].clear(), 'frontend')
    reject('different public CODE descriptor', lambda s,r:s['spec']['public'].__setitem__(72,1), 'preparation')
    for index in [43,44,45,46,50]:
        reject('altered published exit '+str(index),
               lambda s,r,i=index:s['spec']['public'].__setitem__(i,s['spec']['public'][i]^1), 'cryptographic')
    reject('substituted source commitment', lambda s,r:s['roots'].__setitem__(0,'00'*48), 'cryptographic')
    reject('truncated proof', lambda s,r:wire[:-1], 'cryptographic')
    reject('trailing proof bytes', lambda s,r:wire+b'\0', 'cryptographic')
    if args.gkr:
        other = (PACKAGE / 'results/pq384-code-table-long193/proof.bin').read_bytes()
        reject('direct-profile proof substitution', lambda s,r:other, 'cryptographic')
    report = dict(status='PASS', fresh_verifier=json.loads(fresh.stdout), rejections=rejected,
                  proof_bytes=len(wire), statement_json_bytes=(fixture/'statement.json').stat().st_size,
                  request_json_bytes=(fixture/'request.json').stat().st_size,
                  proof_sha256=hashlib.sha256(wire).hexdigest(),
                  limits=['Existing proof reused; no prover or secure parameter changes',
                          'Acceptance to literal HoldsP and quantum soundness remain unproved',
                          'Published exit contains status, fast gas and stack; not full NEAR state'])
    report['total_transported_bytes'] = sum(report[k] for k in ('proof_bytes','statement_json_bytes','request_json_bytes'))
    (fixture/'slice-frontend-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
