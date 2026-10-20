"""Lean packed functional vs executable lane_weights and lane_weight_mle.
Includes zero-padded partial column lanes and zero/one challenge factors.
"""
import argparse
import hashlib
import json
from pathlib import Path
from pq384_terminal_input_weights import lane_weights, lane_weight_mle, mle
from pq384_primitives import P
from pq384_one_fold import ZERO
from check_whir_handoff import add, mul


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean-export', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    raw = a.lean_export.read_bytes()
    cases = json.loads(raw)
    entries = 0
    for n, q, width, point, u, current, nxt, weights, coefficients, functional, at in cases:
        embed = lambda xs: [(x,0,0,0) for x in xs]
        expected = lane_weights(embed(point), embed(current), embed(nxt))
        assert expected == embed(weights)
        assert lane_weight_mle(embed(point), embed(current), embed(nxt), embed(u)) == (at,0,0,0)
        assert mle(expected, embed(u)) == (at,0,0,0)
        assert sum(x*y for x,y in zip(weights, coefficients)) % P == functional
        total = ZERO
        for col in range(2**q):
            values = [(r*r+19*r+7*col+13*r*col)%P if col<width else 0 for r in range(2**n)]
            rows = embed(values)
            total = add(total, add(mul((current[col],0,0,0), mle(rows,embed(point))),
                                   mul((nxt[col],0,0,0), mle(rows[1:]+rows[:1],embed(point)))))
        assert total == (functional,0,0,0)
        entries += len(weights)
    assert len(cases) == 48
    report = dict(status='PASS',cases=len(cases),packed_coefficient_positions=entries,
                  lean_export_sha256=hashlib.sha256(raw).hexdigest(),
                  scope='Actual Python lane_weights/lane_weight_mle vs executable Lean packed weights and functional, partial zero-padded lanes and base-field embedded challenges. Not native commitment refinement or quantum security.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
