"""Exact arithmetic for the checked ideal rate-shift composition theorem.

This instantiates the error bound, not an executable secure protocol. In
particular the diagnostic currently discloses terminal coefficients and does
not implement the continuation strategy assumed here.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
from pq384_ext8_reference import P


def terms(source_queries, continuation_queries):
    field = P ** 8
    return {
        'virtual_extraction': Fraction(64 + 32, field),
        'source_sampling': Fraction(24, 32) ** source_queries,
        'mixing': Fraction(source_queries + 1, field),
        'continuation_extraction': Fraction(32 + 16 + 8, field),
        'continuation_sampling': Fraction(45, 64) ** continuation_queries,
    }


def run():
    # Prior D32/N128, two skipped folds. Continuation D8/N64, three folds.
    assert 2 * 128 + 32 < 3 * 97
    assert 97 <= 2 ** 2 * 25
    assert 2 * 64 + 8 < 3 * 46
    assert 64 <= 46 + 18 and 2 * 18 + 8 <= 64
    target = Fraction(1, 2 ** 128)
    profiles = []
    for qs, qc in [(4, 256), (314, 256)]:
        values = terms(qs, qc)
        bound = sum(values.values(), Fraction())
        # Independently normalize the finite Cartesian count bound as stated
        # in Lean; include the two explicit scaling factors on its left side.
        f = P ** 8
        outer_count = f ** 2 * 32 ** qs
        continuations = f ** 3 * 64 ** qc
        inner_count = f * continuations
        source_limit = 96 * f ** 2 * 32 ** qs + f ** 3 * 24 ** qs
        continuation_limit = ((qs + 1) * continuations * f
                              + f * (56 * f ** 3 * 64 ** qc + f ** 4 * 45 ** qc))
        normalized = Fraction(source_limit * inner_count * f
                              + outer_count * continuation_limit * f,
                              outer_count * inner_count * f * f)
        assert normalized == bound
        profiles.append(dict(source_queries=qs, continuation_queries=qc,
            below_interactive_2powminus128=bound <= target,
            error_bound_float=float(bound),
            terms={k: dict(numerator=str(v.numerator), denominator=str(v.denominator))
                   for k, v in values.items()}))
    assert not profiles[0]['below_interactive_2powminus128']
    assert profiles[1]['below_interactive_2powminus128']
    source_min = next(q for q in range(1000) if sum(terms(q, 256).values()) <= target)
    continuation_min = next(q for q in range(1000) if sum(terms(314, q).values()) <= target)
    here = Path(__file__).resolve()
    report = dict(status='EXACT_IDEAL_BOUND_ONLY', profiles=profiles,
        minimum_source_queries_with_256_continuation_queries=source_min,
        minimum_continuation_queries_with_314_source_queries=continuation_min,
        parameters=dict(source_degree=32, source_domain=128, source_threshold=97,
            skipped_folds=2, folded_domain=32, minimum_agreement=25,
            continuation_degree=8, continuation_domain=64, continuation_threshold=46,
            candidate_radius=18, continuation_folds=3, field_order=str(P ** 8)),
        limitations=['Ideal uniform independent field and query samples only.',
            'Original no-candidate premise, field/root geometry and causal strategy bindings required.',
            'No commitment binding or quantum Fiat-Shamir reduction.',
            'Not a proof-size, full NEAR, 1 Pgas or executable protocol security certificate.'],
        source_sha256=hashlib.sha256(here.read_bytes()).hexdigest())
    (here.parents[2] / 'results/rate-shift-composed-budget.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'profiles'}, indent=2))


if __name__ == '__main__':
    run()
