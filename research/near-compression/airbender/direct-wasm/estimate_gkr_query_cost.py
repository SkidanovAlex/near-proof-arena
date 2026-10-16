"""Expected current-layout authentication costs; no secure parameter selection."""
import argparse
import json
from fractions import Fraction
from pathlib import Path
import pq384_gkr_bus as bus
from estimate_joint_source_cost import expected_counts, validate


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('statement', type=Path)
    ap.add_argument('binary_report', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    spec = json.loads(args.statement.read_text())['spec']
    report = json.loads(args.binary_report.read_text())
    bus.validate(spec)
    stages = []
    degrees = []
    for i, table in enumerate(spec['air']['tables']):
        for width, packing in ((table['width'], spec['source_packings'][i]),
            (4*bus.aux.layout(table)['aux_columns'], spec['aux_packings'][i])):
            if not width:
                continue
            degree = (1 << spec['log_rows'][i])*packing
            degrees.append(degree)
            stages.append((2*degree, 8*((width+packing-1)//packing)))
    D = max(degrees)
    fold_stages = [(D >> i, 32) for i in range(D.bit_length()-1)]
    fixed = sum(report[k] for k in ('air_roots_finals_zerocheck_prefix',
        'gkr_field_bytes', 'opening_length_frame', 'weighted_joint_header'))
    scenarios = []
    for q in (8, 309, 463, 617):
        components = {}
        for label, group in (('source', stages), ('fold', fold_stages)):
            leaves = siblings = Fraction(0)
            for count, leaf_bytes in group:
                l, s = expected_counts(count, q)
                leaves += l*leaf_bytes; siblings += s*48
            components[label+'_leaf_bytes'] = float(leaves)
            components[label+'_sibling_bytes'] = float(siblings)
        scenarios.append(dict(queries=q, expected_total_bytes=fixed+sum(components.values()), **components))
    result = dict(status='PASS', exhaustive_expectation_cases=validate(),
        authenticated_source_branches=len(stages), fixed_bytes=fixed,
        scenarios=scenarios, assumptions=[
            'Uniform independent queries with replacement; expected size, not a bound or measured proof.',
            'Retains current commitments, source packing, 32-bit field transport and SHA384 paths.',
            'Uses current GKR/zerocheck transcript dimensions; does not adjust extension field or degrees.',
            '309/463/617 only illustrate the conditional (3/4)^q tail at128/192/256bits.',
            'Other protocol errors and QROM losses excluded; no secure parameter choice is certified.'])
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
