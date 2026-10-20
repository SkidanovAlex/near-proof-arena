"""Compare measured hash partition under the existing conditional query ledger.

Neither the extension/hash choices nor the quantum compiler are instantiated.
Frozen workload and optional free column/cache work are optimistic assumptions.
"""
import hashlib
import itertools
import json
from pathlib import Path

from screen_swirl_stacking_geometry import cost

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/swirl-security-review/split-geometry'


def main():
    profiles = {
        'baseline': dict(cells=14447856, cached=393216, column_claims=2694,
                         constraint_fixed=159, framing_base=885),
        'split': dict(cells=9670384, cached=393216, column_claims=2995,
                      constraint_fixed=161, framing_base=905),
    }
    baselines = {}
    for name, args in profiles.items():
        b = cost(**args, height=20, log_rate=4, fold=4, terminal=10,
                 extension=4, digest=32, supplied_queries=[61, 30, 20],
                 remove_columns=False)
        assert b['raw_paths_bytes'] == {'baseline': 242809, 'split': 231997}[name]
        baselines[name] = b
    # The split's decoded field/hash counts independently reproduce its wire size.
    assert 5007*16 + 10753*4 + 3374*32 + 905 == 231997
    records = []
    for name, remove_columns, public_cached in itertools.product(profiles, (False, True), (False, True)):
        options = []
        for h in range(15, 26):
            for rate in range(2, 28-h):
                for fold in range(1, 9):
                    for terminal in range(1, 13):
                        rounds = (h-terminal+fold-1)//fold
                        if h-rounds*fold < 0:
                            continue
                        options.append(cost(**profiles[name], height=h, log_rate=rate,
                            fold=fold, terminal=terminal, extension=9, digest=52,
                            remove_columns=remove_columns, public_cached=public_cached))
        best = min(options, key=lambda x: x['expected_frontier_bytes'])
        record = dict(profile=name, free_column_reduction=remove_columns,
                      free_cached_work=public_cached, screened=len(options), best=best,
                      below_target=sum(x['expected_frontier_bytes'] < 300000 for x in options))
        records.append(record)
        print(name, remove_columns, public_cached, best['expected_frontier_bytes'])
    paths = [ROOT/'results/swirl-security-review/hash-split/report.json',
             OUT/'wire.log.gz', Path(__file__),
             Path(__file__).with_name('screen_swirl_stacking_geometry.py'),
             Path(__file__).with_name('screen_swirl_query_payload.py')]
    pins = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/'report.json').write_text(json.dumps(dict(baselines=baselines, records=records,
        sha256=pins, security_certified=False,
        scope='Conditional C=1,Q=2^128,zero grinding credit,each query term separately granted half budget; extension9/digest52 sensitivity only.',
        limitations=['Frozen measured trace despite changed fields/hashes/queries.',
                     'Free-column rows omit the entire replacement argument.',
                     'Free-cache rows omit cached evaluation and binding work.',
                     'Expected frontier cost is not a deterministic bound.',
                     'No QROM, full soundness, full NEAR or stable recursive-key certification.']), indent=2)+'\n')


if __name__ == '__main__':
    main()
