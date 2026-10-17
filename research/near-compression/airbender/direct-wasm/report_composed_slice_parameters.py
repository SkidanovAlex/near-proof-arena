#!/usr/bin/env python3
"""Exact conditional source-valid bound screen on retained Ext4 geometry."""
import argparse
import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'generic-air'))
from check_slice_bus_budget import budget as bus_budget
from report_joint_pcs_parameters import P, numerator, normalized_bound, original_bound


def local_coefficient(residuals, row_log, degree):
    return residuals - 1 + row_log + (degree + 1) * row_log


def literal_composition(field, logs, residuals, degrees, rounds, common_log,
                        input_log, queries, threshold, bus, selected):
    """Evaluate unnormalized count terms, then divide by experiment size*S."""
    assert field > 0 and len(logs) == len(residuals) == len(degrees) == 2
    histories = field**2
    assert min(selected) >= 0 and sum(selected) <= histories
    prefixes = [field**(2*r+1) for r in logs]
    domain = 4 * 2**common_log
    paths = field**sum(2*m+1 for m in rounds)
    pcs_tail = field**(2*common_log) * domain**queries
    evaluated = paths * pcs_tail
    downstream = field * evaluated
    continuation = prefixes[0] * prefixes[1] * downstream
    repair = evaluated*field + field*sum(4*m+1 for m in rounds)*evaluated
    local0 = selected[0] * (local_coefficient(residuals[0], logs[0], degrees[0]) * prefixes[0] * prefixes[1] * downstream + prefixes[0] * prefixes[1] * repair)
    local1 = selected[1] * prefixes[0] * (local_coefficient(residuals[1], logs[1], degrees[1]) * prefixes[1] * downstream + prefixes[1] * repair)
    assert rounds[-1] == input_log
    joint_dimension = sum(logs)+2*input_log+1+common_log
    merged_count = original_bound(field, sum(logs), input_log, common_log, queries, threshold) * field**(joint_dimension+common_log+1) * domain**queries
    assert merged_count.denominator == 1
    initial_counts = field**(sum(logs)+2)
    earlier_paths = field**sum(2*m+1 for m in rounds[:-1])
    concrete_pcs = histories * initial_counts * field * earlier_paths * merged_count.numerator
    return Fraction(bus*field*continuation*field + local0 + local1 + concrete_pcs,
                    histories*continuation*field)


def normalized(field, logs, residuals, degrees, rounds, common_log, input_log,
               queries, threshold, bus, selected):
    repair = 1 + sum(4*m+1 for m in rounds)  # two batched table claims
    local = sum(Fraction(k, field**2) * (local_coefficient(m, r, d)+repair)
                for k, m, r, d in zip(selected, residuals, logs, degrees))
    return (Fraction(bus, field) + local/field +
            normalized_bound(field, sum(logs), input_log, common_log, queries, threshold))


def validate():
    cases = 0
    for field in (2, 3, 7):
        for logs in ([1, 1], [1, 2]):
            for rounds in ([2], [1, 2]):
                for queries in (0, 1, 3):
                    for selected in ((0, 0), (field**2, 0), (0, field**2), (1, field**2-1)):
                        args = (field, logs, [3, 5], [2, 3], rounds, 2, 2, queries, 13, 19, selected)
                        assert literal_composition(*args) == normalized(*args)
                        cases += 1
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    paths = dict(statement=Path('results/pq384-literal193-gkr-fixed13/statement.json'),
                 proof=Path('results/pq384-literal193-gkr-fixed13/proof.json'),
                 manifest=Path('results/literal193-fixed-rebuild.report.json'),
                 reference_statement=Path('results/pq384-code-table-long193/statement.json'),
                 degrees=Path('results/pq384-code-table-long193/combined-degree-report.json'),
                 bus=Path('results/pq384-code-table-long193/bus-budget.json'))
    data = {k: json.loads(p.read_text()) for k, p in paths.items()}
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    for key in ('statement', 'proof'):
        assert sha(paths[key]) == data['manifest'][key+'_sha256']
    spec = data['statement']['spec']
    for key in ('air', 'public', 'log_rows'):
        assert spec[key] == data['reference_statement']['spec'][key]
    logs = spec['log_rows']
    assert len(logs) == 2 and all(r > 0 for r in logs)
    residuals, degrees = [], []
    for t in range(2):
        cases = [c for c in data['degrees']['cases'] if c['table'] == t]
        shape = {(c['source_residuals']+c['auxiliary_residuals'], c['verifier_residual_degree']) for c in cases}
        assert len(shape) == 1
        m, d = shape.pop()
        residuals.append(m); degrees.append(d)
    bus = bus_budget(spec)['joint_error_numerator']
    assert bus == data['bus']['literal_lean_budget']['numerator']
    round_counts = [len(layer['rounds']) for layer in data['proof']['gkr']['layers']]
    assert all(r > 0 and r % 2 == 0 for r in round_counts)
    rounds = [r//2 for r in round_counts]
    input_log = data['manifest']['input_log']
    assert rounds[-1] == input_log
    packings = spec['source_packings'] + spec['aux_packings']
    assert all(p > 0 and p & (p-1) == 0 for p in packings)
    common_log = max(r+p.bit_length()-1 for r, s, a in zip(logs, spec['source_packings'], spec['aux_packings']) for p in (s, a))
    domain = 4*2**common_log
    threshold = (2*domain+2**common_log)//3+1
    repair = 1+sum(4*m+1 for m in rounds)
    local = [local_coefficient(m,r,d)+repair for m,r,d in zip(residuals,logs,degrees)]
    pcs = numerator(sum(logs), input_log, common_log)
    coefficient = bus+max(local)+pcs
    screens = []
    for extension in (4,8,12):
        field = P**extension
        for bits in (128,192,210,214,215,256):
            target = Fraction(1,2**bits)
            challenge = Fraction(coefficient,field)
            row = dict(extension_degree=extension, target_ideal_bits=bits, feasible_for_this_bound=challenge<target)
            if challenge<target:
                q = 0
                while challenge+Fraction(threshold-1,domain)**q > target: q += 1
                assert q == 0 or challenge+Fraction(threshold-1,domain)**(q-1) > target
                worst = (field**2,0) if local[0]>=local[1] else (0,field**2)
                exact = literal_composition(field, logs, residuals, degrees, rounds, common_log, input_log, q, threshold, bus, worst)
                assert exact == challenge+Fraction(threshold-1,domain)**q
                row.update(minimum_queries=q, bound_numerator=exact.numerator, bound_denominator=exact.denominator)
            screens.append(row)
    report = dict(status='CONDITIONAL_SOURCE_VALID_COMPOSED_BOUND_GEOMETRY_PROJECTION',
        theorem='NearCompression.prepared_concrete_soundness_budget',
        inputs={k:dict(path=str(p),sha256=sha(p)) for k,p in paths.items()},
        geometry=dict(row_logs=logs,residual_counts=residuals,degrees=degrees,gkr_layer_logs=rounds,input_log=input_log,common_log=common_log,threshold=threshold),
        terms=dict(bus=bus,local_with_batching_and_gkr=local,pcs=pcs,total_challenge_numerator=coefficient),
        normalized_upper_bound='(bus + max(local0,local1) + pcs)/fieldSize + ((T-1)/N)^queries',
        branch_reason='Disjoint selected-history counts total at most fieldSize^2; maximize their weighted average, not sum two full-history budgets.',
        challenge_only_ideal_bit_ceiling={str(e):e*math.log2(P)-math.log2(coefficient) for e in (4,8,12)},
        cases=screens,validation=dict(exact_literal_vs_normalized_cases=validate(),query_minimality_checked=True,retained_manifest_hashes_checked=True),
        limitations=['Source-valid branch only; source-invalid branch integration remains separate.',
            'Semantic and ideal-oracle assumptions of the theorem are not instantiated by this arithmetic report.',
            'Ext8/Ext12 are field-size projections of retained Ext4 circuit/packing geometry; no native Ext8 size or GKR-layout measurement.',
            'Independent uniform ideal challenges only; no hash/Fiat-Shamir/QROM or 128-bit post-quantum claim.',
            'Python count normalization is independently checked exactly but is not a new Lean normalization theorem.',
            'No proof-byte estimate or generated secure proof. Bounds failing a target are not attacks.'])
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(terms=report['terms'],ceilings=report['challenge_only_ideal_bit_ceiling'],cases=[{k:v for k,v in r.items() if not k.startswith('bound_')} for r in screens],validation=report['validation']),indent=2))

if __name__ == '__main__': main()
