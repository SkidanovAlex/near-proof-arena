"""Counterfactual query-only geometry; does not change accepted security parameters."""
import json
import random
from fractions import Fraction
from pathlib import Path
from screen_ext8_packing import choose, fold_cost, total

UPSTREAM = "afec1fac27c1c8cc7331aa5668bc9800f104d92c"


def minimum_queries(factor, bits):
    q = 0
    while factor ** q > Fraction(1, 2 ** bits):
        q += 1
    assert factor ** q <= Fraction(1, 2 ** bits)
    assert q == 0 or factor ** (q - 1) > Fraction(1, 2 ** bits)
    return q


def main():
    records = []
    # rho=1/4; Johnson canonical slack=sqrt(rho)/20=1/40.
    for regime, factor in (("current_extraction", Fraction(3, 4)),
                           ("upstream_unique", Fraction(5, 8)),
                           ("upstream_johnson", Fraction(21, 40))):
        q = minimum_queries(factor, 128)
        for layout, widths in (("separate", [605, 24, 198, 400]),
                               ("pooled_by_phase", [803, 424])):
            winners = []
            for seed in range(8):
                candidates = []
                for exponent in range(11):
                    degree = 256 * 2 ** exponent
                    rng = random.Random(82501 + seed * 100 + exponent)
                    samples = [rng.randrange(4 * degree) for _ in range(q)]
                    selected = choose(widths, 256, degree, samples)
                    if selected is None:
                        continue
                    sources, branches = selected
                    size = sources + total(fold_cost(degree, samples)) + 40 + 240 * (degree.bit_length()-1)
                    candidates.append(dict(degree=degree, packing=[b['packing'] for b in branches],
                                           opening_bytes=size, subtotal_bytes=size+51328))
                winners.append(min(candidates, key=lambda x: x['opening_bytes']))
            records.append(dict(regime=regime, factor=str(factor), isolated_query_bits=128,
                                queries=q, layout=layout, winners=winners,
                                min_subtotal_bytes=min(w['subtotal_bytes'] for w in winners),
                                max_subtotal_bytes=max(w['subtotal_bytes'] for w in winners)))
    report = dict(status="COUNTERFACTUAL_QUERY_ONLY_SCREEN", upstream_commit=UPSTREAM,
                  source="src/protocols/params/regime.rs:one_minus_distance_log2",
                  source_sha256="8b621e391eeb6f039d0f4aec14b717859111f126d07f2461ac1e8c8a5f24a70a",
                  records=records,
                  scope="Exact rational query counts; simulated existing binary-fold codec geometry. "
                        "Upstream unique/Johnson proximity bounds are NOT proved for our protocol. "
                        "Excludes extraction, list, OOD, mixing, composition, Fiat-Shamir and quantum losses. "
                        "Not a WHIR proof-size estimate: WHIR code switching changes geometry. "
                        "Pooling and alternate packing unimplemented; excludes public envelope. "
                        "No capacity conjecture or grinding used; no feasibility gate changed.")
    out=Path(__file__).resolve().parents[2]/'results/whir-query-regime-screen.json'
    out.write_text(json.dumps(report, indent=2)+'\n')
    for r in records:
        print(r['regime'], r['layout'], r['queries'], r['min_subtotal_bytes'], r['max_subtotal_bytes'])

if __name__ == '__main__':
    main()
