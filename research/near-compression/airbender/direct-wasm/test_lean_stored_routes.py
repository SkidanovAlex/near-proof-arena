"""Full retained route captures through Lean's proved checker; not kernel instances."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--capture', action='append', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    reports = []
    def run(path):
        start = time.monotonic()
        result = subprocess.run(['lake', 'env', 'lean', '--run', 'CheckStoredRoutes.lean', str(path)],
                                text=True, capture_output=True, timeout=120)
        return result, time.monotonic()-start
    for path in args.capture:
        original = json.loads(path.read_text())
        result, seconds = run(path)
        if result.returncode:
            raise RuntimeError(result.stdout+result.stderr)
        checked = json.loads(result.stdout)
        assert checked['status'] == 'PASS'
        assert checked['nodes'] == len(original['circuit']['nodes'])
        assert checked['layers'] == len(original['layout']['layers'])
        assert checked['gates'] == sum(map(len, original['layout']['layers']))
        mutations = []
        def mutation(label, fn):
            value = copy.deepcopy(original)
            fn(value)
            mutations.append((label, value))
        mutation('wrong-zero-gate', lambda x: x['layout']['layers'][0].__setitem__(0, ['sub',0,0]))
        mutation('missing-final-root', lambda x: x['certificate']['plans'][-1].pop(str(x['circuit']['root'])))
        mutation('invalid-source-node', lambda x: x['certificate']['plans'][0].__setitem__(str(len(x['circuit']['nodes'])), 1))
        mutation('out-of-range-live-position', lambda x: x['certificate']['plans'][-1].__setitem__(str(x['circuit']['root']),len(x['layout']['layers'][-1])))
        mutation('unknown-opcode', lambda x: x['layout']['layers'][0].__setitem__(0,['xor',0,0]))
        rejected = []
        with tempfile.TemporaryDirectory(prefix='near-lean-routes-') as directory:
            for label, value in mutations:
                target = Path(directory)/(label+'.json')
                target.write_text(json.dumps(value, separators=(',', ':')))
                bad, _ = run(target)
                assert bad.returncode != 0, label
                output = (bad.stdout+bad.stderr).strip()
                # Reject runtime/parser failures only; a Lean elaboration failure
                # must not masquerade as a malformed-certificate rejection.
                assert 'error:' not in output and 'uncaught exception:' in output, output
                rejected.append(dict(case=label, reason=output))
        reports.append(dict(capture=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                            result=checked,seconds=seconds,rejected=rejected))
    report = dict(status='PASS',captures=reports,
                  adapter_sha256=hashlib.sha256(Path('CheckStoredRoutes.lean').read_bytes()).hexdigest(),
                  scope='Full JSON instances executed by the Lean checker; generic checker soundness is kernel-proved, these concrete results are not kernel-reduced proof terms.',
                  remaining=['Parser refinement, kernel certificates for captures, initial placement/acyclicity certificates, full cryptographic soundness.'])
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],captures=len(reports),rejections=sum(len(r['rejected']) for r in reports))))


if __name__ == '__main__': main()
