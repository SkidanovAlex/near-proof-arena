"""Same-artifact proof verification versus independently executed Lean runCall."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

from verify_prepared_slice import PACKAGE


def main():
    fixture = PACKAGE / 'results/pq384-code-table-long193'
    out = PACKAGE / 'results/slice-execution-binding'
    out.mkdir(exist_ok=True)
    statement = json.loads((fixture / 'statement.json').read_text())
    pub = statement['spec']['public']
    fuel = 1 << statement['spec']['log_rows'][0]
    commands = [
        [sys.executable, str(Path(__file__).with_name('verify_prepared_slice.py')),
         str(fixture / 'proof.bin'), str(fixture / 'statement.json'), str(fixture / 'request.json')],
        ['lake', 'env', 'lean', '--run', 'PreparedSliceOracle.lean',
         str(fixture / 'request.json'), str(fuel)],
    ]
    records = []
    for command in commands:
        start = time.monotonic()
        result = subprocess.run(command, cwd=PACKAGE, capture_output=True, text=True, check=True)
        records.append(dict(output=json.loads(result.stdout), seconds=time.monotonic()-start))
    assert records[0]['output']['status'] == 'PASS'
    # Decode limb values independently of the Lean public-output helper.
    assert 0 <= pub[43] <= 8
    published = dict(done=pub[44] == 1, failed=pub[45] == 1,
                     gas=sum(pub[46+i] << (16*i) for i in range(4)),
                     stack=[pub[50+2*i] + (pub[51+2*i] << 16) for i in range(pub[43])])
    assert published == records[1]['output'], (published, records[1])
    # Exercise the actual verifier with incorrect public outputs. A process failure
    # counts only when it reaches a proof-relation check, not preparation or parsing.
    negatives = []
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'statement.json'
        for i in [43, 44, 45, 46, 50]:
            altered = json.loads((fixture / 'statement.json').read_text())
            altered['spec']['public'][i] ^= 1
            path.write_text(json.dumps(altered))
            command = commands[0].copy()
            command[-2] = str(path)
            result = subprocess.run(command, cwd=PACKAGE, capture_output=True, text=True)
            assert result.returncode != 0, i
            assert 'literal runCall eligibility rejected' not in result.stderr, result.stderr
            assert 'Traceback' in result.stderr, result.stderr
            # Retain full evidence; classify precise last error below, never a bare exit code.
            error = result.stderr.strip().splitlines()[-1]
            assert error == 'ValueError: table zerocheck', error
            negatives.append(dict(public_index=i, error=error))
            (out / f'negative-{i}.log').write_text(result.stderr)
    report = dict(status='PASS', published=published, processes=records, negatives=negatives,
                  execution_fuel=fuel,
                  artifacts={name: dict(bytes=(fixture/name).stat().st_size,
                    sha256=hashlib.sha256((fixture/name).read_bytes()).hexdigest())
                    for name in ['proof.bin', 'statement.json', 'request.json']},
                  limitations=['Retained proof, not fresh proving or malicious-witness proving.',
                    'No recursive parent consumes this slice proof yet.',
                    'Diagnostic Q8/Ext4; no PQ128 or cryptographic acceptance-to-HoldsP theorem.',
                    'Bounded i32 slice, not full NEAR state transition.'])
    report['total_transported_bytes'] = sum(x['bytes'] for x in report['artifacts'].values())
    (out / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
