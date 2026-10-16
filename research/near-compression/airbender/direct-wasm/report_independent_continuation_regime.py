"""Exact screening of available binary-fold theorem premises, not a profile."""
import json
from pathlib import Path


def query_term_count(n, threshold, bits=128):
    # Isolated (T-1)/N query term only; excludes every other error term.
    q = 0
    while pow(threshold-1, q)*(1 << bits) > pow(n, q):
        q += 1
    return q


def main():
    root = Path(__file__).resolve().parents[2]
    prior = json.loads((root/'results/independent-mixing-candidates/report.json').read_text())
    records = []
    for stage in prior['stages']:
        n, d, t = (stage[k] for k in ('domain_size','degree','required_agreement'))
        minimum = (2*n+d)//3+1
        assert 2*n+d < 3*minimum
        assert not 2*n+d < 3*(minimum-1)
        records.append(dict(stage, binary_fold_regime_holds=2*n+d < 3*t,
            minimum_binary_fold_threshold=minimum,
            isolated_128bit_query_term_at_johnson_threshold=query_term_count(n,t),
            isolated_128bit_query_term_at_binary_fold_threshold=query_term_count(n,minimum)))
    print(json.dumps(dict(stages=records, scope=
        'The existing general_checked_interactive_fold_soundness theorem has a high-agreement premise. '
        'Its regime fails at every listed Johnson threshold. Query counts screen one ideal classical '
        'term only; neither column is an accepted code-switch/PQ128 parameter schedule. The binary '
        'fold continuation theorem is not a theorem for the implemented rate-changing chain.'), indent=2))


if __name__ == '__main__':
    main()
