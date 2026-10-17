"""Full-profile transcript and mandatory-opening rejection regressions."""
import argparse
import copy
import json
from pathlib import Path
import pq384_gkr_bus as bus


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('directory', type=Path)
    ap.add_argument('report', type=Path)
    ap.add_argument('--seed-profile', action='store_true')
    args = ap.parse_args()
    proof = json.loads((args.directory/'proof.json').read_text())
    statement = json.loads((args.directory/'statement.json').read_text())
    spec = statement['spec']; roots = list(map(bytes.fromhex, statement['roots']))
    if args.seed_profile:
        import pq384_seed_gkr_bus as seed
        config = seed.configure(spec['air'])
        verify = lambda p, s, r: seed.verify(p, s, r, config)
    else:
        verify = bus.verify
    assert verify(proof, spec, roots)
    passed = []
    def reject(name, p=proof, s=spec, r=roots):
        try:
            verify(p, s, r)
        except ValueError:
            passed.append(name)
        else:
            raise AssertionError(name)
    p = copy.deepcopy(proof); del p['opening']; reject('missing-opening', p)
    p = copy.deepcopy(proof); p['opening']['queries'] = []; reject('empty-opening-queries', p)
    p = copy.deepcopy(proof)
    p['opening']['queries'][0]['sources'][0]['leaf'][0] ^= 1
    reject('altered-source-leaf', p)
    p = copy.deepcopy(proof)
    p['gkr']['layers'][-1]['inputs'][0][0] = (p['gkr']['layers'][-1]['inputs'][0][0]+1)%bus.old.P
    reject('altered-final-gkr-input', p)
    p = copy.deepcopy(proof)
    p['tables'][-1][0][0][0] = (p['tables'][-1][0][0][0]+1)%bus.old.P
    reject('altered-last-table-constraint', p)
    s = copy.deepcopy(spec); s['public'][0] = (s['public'][0]+1)%bus.old.P
    reject('altered-public-input', s=s)
    r = list(roots); r[0] = bytes([r[0][0]^1])+r[0][1:]
    reject('altered-source-root', r=r)
    if args.seed_profile:
        for key in ('digest', 'compiler'):
            bad_config = copy.deepcopy(config)
            bad_config[key] = bytes([bad_config[key][0]^1])+bad_config[key][1:]
            try:
                seed.verify(proof, spec, roots, bad_config)
            except ValueError:
                passed.append('altered-config-'+key)
            else:
                raise AssertionError(key)
    report = dict(status='PASS', tables=len(proof['tables']), rejections=passed,
                  scope='Complete verifier checks mandatory PCS and transcript bindings; finite tests only')
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
