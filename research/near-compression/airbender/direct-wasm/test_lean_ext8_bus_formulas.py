"""Run the Lean Ext8 certificate checker and require runtime rejection.
Certificate checks are not universal generator refinement or PCS extraction.
"""
import argparse, copy, hashlib, json, subprocess, tempfile
from pathlib import Path


def run(path, positive, expanded=False):
    p = subprocess.run(['lake', 'env', 'lean', '--run', 'CheckExt8BusFormulas.lean', *(['--expanded'] if expanded else []), str(path)],
        capture_output=True, text=True, timeout=90)
    text = p.stdout+p.stderr
    if positive:
        if p.returncode: raise RuntimeError(text)
        result = json.loads(p.stdout.strip().splitlines()[-1])
        assert result['status'] == 'PASS'
        return result
    if not p.returncode or 'uncaught exception:' not in text or 'error:' in text:
        raise RuntimeError('Expected runtime rejection, got: '+text)
    return text.strip().splitlines()[-1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--capture', type=Path, required=True)
    parser.add_argument('--expanded', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); original = json.loads(args.capture.read_text())
    good = run(args.capture, True, args.expanded)
    def residual(x): return x[0]['residuals'][0]
    def coherent_wrong(x):
        r = residual(x)
        r['formula'] = ['lit', [0]*8]
        r['instructions'] = [[0, 0, 0]+[0]*8]
        r['root'] = 0
        r['expected'] = [0]*8
    mutations = [
        ('coherent-wrong-specification', coherent_wrong),
        ('changed-bus-id', lambda x: x[3]['table']['interactions'][0].__setitem__('bus', 13)),
        ('changed-bus-challenge', lambda x: x[1]['alpha'].__setitem__(0, (x[1]['alpha'][0]+1)%2013265921)),
        ('changed-final', lambda x: x[1]['finals'][0].__setitem__(0, (x[1]['finals'][0][0]+1)%2013265921)),
        ('omitted-residual', lambda x: x[0]['residuals'].pop()),
        ('reordered-residuals', lambda x: x[0]['residuals'].reverse()),
        ('wrong-root', lambda x: residual(x).__setitem__('root', len(residual(x)['instructions']))),
        ('unknown-opcode', lambda x: residual(x)['instructions'][0].__setitem__(0, 99)),
        ('truncated-instruction', lambda x: residual(x)['instructions'][0].pop()),
        ('noncanonical-constant', lambda x: residual(x)['instructions'][0].__setitem__(3, 2013265921)),
        ('noncanonical-coordinate', lambda x: x[0]['current'].__setitem__(0, 2013265921)),
        ('truncated-selector', lambda x: x[0]['selectors']['first'].pop()),
        ('wrong-expected-value', lambda x: residual(x)['expected'].__setitem__(0, (residual(x)['expected'][0]+1)%2013265921)),
        ('cyclic-root', lambda x: residual(x)['instructions'][residual(x)['root']].__setitem__(1, residual(x)['root'])),
        ('empty-capture', lambda x: x.clear()),
        ('empty-residuals', lambda x: x[0]['residuals'].clear()),
    ]
    rejected = []
    with tempfile.TemporaryDirectory(prefix='ext8-bus-check-') as tmp:
        for name, mutate in mutations:
            bad = copy.deepcopy(original); mutate(bad)
            path = Path(tmp)/'bad.json'; path.write_text(json.dumps(bad))
            rejected.append(dict(case=name, reason=run(path, False, args.expanded)))
    report = dict(status='PASS', positive=good, rejections=rejected,
        capture_sha256=hashlib.sha256(args.capture.read_bytes()).hexdigest(),
        checker_sha256=hashlib.sha256(Path('CheckExt8BusFormulas.lean').read_bytes()).hexdigest(),
        expanded=args.expanded,
        scope='Exact or proved fingerprint-expanded formal bus-spec AST binding, formula routes, acyclicity and sampled values; no full prover or authentication claim.')
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', residuals=good['residuals'], rejections=len(rejected))))

if __name__ == '__main__': main()
