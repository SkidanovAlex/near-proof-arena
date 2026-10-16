"""Executable Lean current/next transform vs actual Python opening weights.
The local inverse transform is an independent test oracle, not native source
commitment refinement. All challenges are base-field embedded.
"""
import argparse
import hashlib
import json
from pathlib import Path
from pq384_terminal_input_weights import row_weights, row_weight_mles, mle
from pq384_primitives import P


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean-export', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    raw = args.lean_export.read_bytes()
    cases = json.loads(raw)
    entries = 0
    mles = 0
    for n, point, values, coefficients, current, nxt, current_mle, next_mle in cases:
        embed = lambda xs: [(x, 0, 0, 0) for x in xs]
        rows = embed(values)
        r, s = row_weights(embed(point))
        assert r == embed(current) and s == embed(nxt)
        # Independent inverse zeta bit passes on the source Boolean values.
        inverse = values[:]
        bit = 1
        while bit < len(inverse):
            for i in range(len(inverse)):
                if i & bit:
                    inverse[i] = (inverse[i] - inverse[i ^ bit]) % P
            bit *= 2
        assert inverse == coefficients
        assert sum(a*b for a,b in zip(coefficients,current)) % P == current_mle
        assert sum(a*b for a,b in zip(coefficients,nxt)) % P == next_mle
        assert mle(rows, embed(point)) == (current_mle,0,0,0)
        assert mle(rows[1:]+rows[:1], embed(point)) == (next_mle,0,0,0)
        for u in [[0]*n, [1]*n, [(71+13*i)%P for i in range(n)]]:
            fast_current, fast_next = row_weight_mles(embed(point), embed(u))
            assert fast_current == mle(r, embed(u))
            assert fast_next == mle(s, embed(u))
            mles += 1
        entries += len(values)
    assert len(cases) == 36
    report = dict(status='PASS',cases=len(cases),coefficient_entries=entries,
                  borrow_dp_vs_explicit_mle_cases=mles,
                  lean_export_sha256=hashlib.sha256(raw).hexdigest(),
                  scope='Lean dual current/cyclic-next weights vs actual Python row_weights, with independent inverse transform and borrow-DP regression. Base-field embeddings only; not native commitment or full implementation proof.')
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
