"""Check extracted two-row snapshots against original combined SHA512 AST."""
import argparse
import json
import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parent.parent/'generic-air'))
import reference


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--air', type=Path, required=True)
    p.add_argument('--rows', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    air = json.loads(a.air.read_text())
    rows = json.loads(a.rows.read_text())['rows']
    blocks = sum(row[5232] for row in rows)//80
    constraints = air['tables'][0]['constraints']
    checks = snapshots = negatives = 0
    for block in range(blocks):
        for phase in [0, 39, 78]:
            start = 80*block+phase
            pair = rows[start:start+2]
            for r in range(2):
                for e in constraints:
                    assert reference.evaluate(e, pair, r, []) == 0, (block, phase, r)
                    checks += 1
            # Break the next-round state bit; the original transition must reject.
            bad = [row[:] for row in pair]
            bad[1][2544] = 1-bad[1][2544]
            assert any(reference.evaluate(e, bad, 0, []) for e in constraints)
            negatives += 1
            snapshots += 1
    report = dict(status='PASS', blocks=blocks, snapshots=snapshots,
                  residual_checks=checks, broken_transition_rejections=negatives,
                  scope='Captured four-block witness, original combined constraints on two-row snapshots at phases0,39,78. Lean theorem covers every eligible segment phase; regression is not proof-acceptance or security evidence.')
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
