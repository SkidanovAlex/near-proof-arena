"""Conditional frozen-workload screen charging the measured GKR replacement.

This is not an instantiated PQ128 protocol or an independent typed wire census.
The framing residual is calibrated against the complete measured binary bundle.
"""
import hashlib
import json
from pathlib import Path
from screen_swirl_stacking_geometry import cost

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'results/swirl-security-review'
OUT = BASE / 'root-bundle-screen'


def main():
    report_path = BASE / 'root-bundle-codec/report.json'
    proof_path = BASE / 'root-bundle-codec/proof.bin'
    report = json.loads(report_path.read_text())
    blob = proof_path.read_bytes()
    assert hashlib.sha256(blob).hexdigest() == report['sha256']
    assert len(blob) == report['bytes']['total'] == 204076
    assert report['bytes']['gkr'] == 1288 * 16
    args = dict(cells=9670384, cached=393216, column_claims=0,
                constraint_fixed=161+1288, framing_base=296)
    baseline = cost(**args, height=20, log_rate=4, fold=4, terminal=10,
                    extension=4, digest=32, supplied_queries=[61,30,20])
    assert baseline['raw_paths_bytes'] == len(blob)
    records = []
    for free_cache in (False, True):
        options = []
        for h in range(15,26):
            for rate in range(2,28-h):
                for fold in range(1,9):
                    for terminal in range(1,13):
                        rounds = (h-terminal+fold-1)//fold
                        if h-rounds*fold < 0:
                            continue
                        options.append(cost(**args, height=h, log_rate=rate,
                            fold=fold, terminal=terminal, extension=9, digest=52,
                            public_cached=free_cache))
        record = dict(free_cached_work=free_cache, screened=len(options),
                      best=min(options,key=lambda x:x['expected_frontier_bytes']),
                      below_target=sum(x['expected_frontier_bytes']<300000 for x in options))
        records.append(record)
        print(json.dumps(record))
    paths = [report_path, proof_path, Path(__file__),
             Path(__file__).with_name('screen_swirl_stacking_geometry.py'),
             Path(__file__).with_name('screen_swirl_query_payload.py')]
    OUT.mkdir(exist_ok=True)
    result = dict(baseline=baseline, records=records, security_certified=False,
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        assumptions=['C=1,Q=2^128,zero grinding credit; each query error independently gets half budget.',
                     'Uninstantiated extension9/digest52 sensitivity; all other security terms omitted.',
                     'Frozen trace and GKR message counts despite changed security and geometry.',
                     '296-byte residual calibrated to bundle; not independent typed census.',
                     'Free-cache variant omits cached evaluation and binding costs.',
                     'Expected Merkle frontier cost is not a deterministic size bound.',
                     'No QROM, recursive closure, full NEAR or Lean composition certification.'])
    (OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
