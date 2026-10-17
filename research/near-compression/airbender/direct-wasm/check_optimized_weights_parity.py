"""Compare executable Lean mutable zeta and borrow DP with prover Python."""
import argparse
import hashlib
import json
from pathlib import Path
from pq384_terminal_input_weights import upper_zeta, row_weights, row_weight_mles, mle


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-export', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.lean_export.read_bytes()
    cases = json.loads(raw)
    entries = 0
    embed = lambda xs: [(x, 0, 0, 0) for x in xs]
    for n, point, u, values, transformed, current, shifted in cases:
        assert len(point) == len(u) == n and len(values) == 2**n
        assert upper_zeta(embed(values)) == embed(transformed)
        expected = ((current, 0, 0, 0), (shifted, 0, 0, 0))
        assert row_weight_mles(embed(point), embed(u)) == expected
        a, b = row_weights(embed(point))
        assert (mle(a, embed(u)), mle(b, embed(u))) == expected
        entries += len(values)
    assert len(cases) == 72
    report = dict(status='PASS', cases=len(cases), transformed_entries=entries,
                  lean_export_sha256=hashlib.sha256(raw).hexdigest(),
                  scope='Executable Lean mutable transform and optimized DP vs actual Python. Dimensions 0..5; zero, one, minus-one and mixed coordinates. Runtime parity uses base-field embeddings; formal algebra is generic over fields. Not a full PCS implementation or cryptographic soundness proof.')
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
