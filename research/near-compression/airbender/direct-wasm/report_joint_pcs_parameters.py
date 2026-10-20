#!/usr/bin/env python3
"""Exact merged PCS component screen; not global/PQ security or a byte estimate."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

P = 2013265921


def numerator(row_coordinates, input_log, common_log):
    domain = 4 * 2**common_log
    dimension = row_coordinates + 2*input_log + 1 + common_log
    fold = sum(max(domain >> (i+1), 2) for i in range(common_log))
    return fold + max(2*common_log, dimension*max(domain, 2))


def original_bound(field, rows, input_log, common_log, queries, threshold):
    """Literal count expressions in gkr_joint_failure_acceptance_count."""
    domain = 4 * 2**common_log
    history = rows + 2*input_log + 1
    dimension = history + common_log
    outer = field**dimension
    inner = field**common_log * domain**queries
    fold = sum(max(domain >> (i+1), 2) for i in range(common_log))
    fold_budget = fold*field**common_log*domain**queries + field**(common_log+1)*(threshold-1)**queries
    near = field**history * (2*common_log*field**common_log*inner + field**common_log*fold_budget)
    far = dimension*max(domain, 2)*field**(dimension-1)*inner*field + outer*fold_budget
    return Fraction(max(near, far), outer*inner*field)


def normalized_bound(field, rows, input_log, common_log, queries, threshold):
    return Fraction(numerator(rows, input_log, common_log), field) + Fraction(threshold-1, 4*2**common_log)**queries


def screen(rows, input_log, common_log, extension, bits):
    field = P**extension
    domain = 4*2**common_log
    threshold = (2*domain + 2**common_log)//3 + 1
    coefficient = numerator(rows, input_log, common_log)
    target = Fraction(1, 2**bits)
    challenge = Fraction(coefficient, field)
    result = dict(extension_degree=extension, target_ideal_bits=bits,
                  challenge_numerator=coefficient, field_size=field,
                  feasible_for_this_bound=challenge < target)
    if challenge >= target:
        result['reason'] = 'Challenge term alone exceeds target; increasing queries cannot certify it with this bound.'
        return result
    queries = 0
    while normalized_bound(field, rows, input_log, common_log, queries, threshold) > target:
        queries += 1
    assert queries == 0 or normalized_bound(field, rows, input_log, common_log, queries-1, threshold) > target
    bound = normalized_bound(field, rows, input_log, common_log, queries, threshold)
    assert bound == original_bound(field, rows, input_log, common_log, queries, threshold)
    result.update(minimum_queries=queries, bound_numerator=bound.numerator, bound_denominator=bound.denominator)
    return result


def validate_normalization():
    cases = 0
    # Independent literal-count evaluation versus normalized rational expression.
    for field in (2, 3, 7):
        for rows in (0, 2):
            for input_log in (0, 2):
                for common_log in (0, 1, 3):
                    domain = 4*2**common_log
                    for threshold in (1, domain//2+1, domain):
                        for queries in (0, 1, 4):
                            assert original_bound(field, rows, input_log, common_log, queries, threshold) == normalized_bound(field, rows, input_log, common_log, queries, threshold)
                            cases += 1
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--statement', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    spec = json.loads(a.statement.read_text())['spec']
    manifest = json.loads(a.manifest.read_text())
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    assert sha(a.statement) == manifest['statement_sha256']
    logs = spec['log_rows']
    assert isinstance(logs, list) and len(logs) == len(spec['source_packings']) == len(spec['aux_packings'])
    degrees = []
    for r, source, auxiliary in zip(logs, spec['source_packings'], spec['aux_packings']):
        for packing in (source, auxiliary):
            assert packing > 0 and packing & (packing-1) == 0
            degrees.append(r + packing.bit_length()-1)
    rows, input_log, common_log = sum(logs), manifest['input_log'], max(degrees)
    assert [t['row_log'] for t in manifest['expected_tables']] == logs
    domain = 4*2**common_log
    threshold = (2*domain+2**common_log)//3+1
    diagnostic = normalized_bound(P**4, rows, input_log, common_log, 8, threshold)
    report = dict(status='CONDITIONAL_MERGED_IDEAL_PCS_PARAMETER_SCREEN',
        theorem='NearCompression.gkr_concrete_joint_failure_count',
        inputs=dict(statement=str(a.statement), statement_sha256=sha(a.statement), manifest=str(a.manifest), manifest_sha256=sha(a.manifest)),
        geometry=dict(row_coordinates=rows, input_log=input_log, common_log=common_log, domain=domain, threshold=threshold),
        normalized_bound='(foldNumerator + max(2*C, jointDimension*max(N,2)))/fieldSize + ((T-1)/N)^queries',
        merged_challenge_numerator=numerator(rows,input_log,common_log),
        diagnostic_q8=dict(numerator=diagnostic.numerator, denominator=diagnostic.denominator),
        cases=[screen(rows,input_log,common_log,e,b) for e in (4,8,12) for b in (128,192,256)],
        validation=dict(exact_normalization_cases=validate_normalization(), minimum_query_boundary_checked=True),
        limitations=['This is an upper-bound feasibility screen, not an attack lower bound.',
            'Original ideal-oracle theorem assumptions remain uninstantiated for the complete executable verifier.',
            'Only the merged PCS component; local AIR, buses, batching, GKR and computational terms are not added into a global security claim.',
            'Extension degrees 8 and 12 here are arithmetic projections, not newly implemented proof profiles.',
            '128 ideal bits is not 128 post-quantum bits; QROM compilation and its losses remain open.',
            'No proof bytes are projected by this script; existing Q309 codec replays are not regenerated secure proofs.'])
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(status=report['status'], geometry=report['geometry'], coefficient=report['merged_challenge_numerator'], cases=[{k:v for k,v in r.items() if k not in ('bound_numerator','bound_denominator','field_size')} for r in report['cases']], validation=report['validation']), indent=2))


if __name__ == '__main__':
    main()
