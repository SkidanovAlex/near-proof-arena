"""Phase-respecting bank partition screen, not an implemented proof profile.

Exhaustively optimizes column-concatenation groups and power-of-two packing in
this finite shape. Logical row rotation remains local to each table, as in
ext8_pooled_weights; source and post-challenge auxiliary banks never mix.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
import model_joint_nibble_geometry as joint

ROOT = joint.ROOT


def best_partition(members, queries, degree_cap):
    assert members and len(members) <= 11
    assert len({m['phase'] for m in members}) == 1
    assert len({m['table'] for m in members}) == len(members)
    assert max(m['rows'] for m in members) <= degree_cap <= joint.FIELD_DEGREE_CAP
    assert degree_cap & (degree_cap - 1) == 0
    banks = {}
    for mask in range(1, 1 << len(members)):
        group = [m for i, m in enumerate(members) if mask >> i & 1]
        rows = max(m['rows'] for m in group)
        width = sum(m['width'] for m in group)
        options = []
        for log_p in range(min((degree_cap // rows).bit_length() - 1, (width - 1).bit_length()) + 1):
            b = joint.branch(rows, width, 1 << log_p)
            b['expected_bytes'] = joint.expected_tree(b['half'], b['leaf_bytes'], queries)
            options.append(b)
        bank = min(options, key=lambda b: b['expected_bytes'])
        offset = 0; blocks = []
        for m in group:
            blocks.append(dict(table=m['table'], rows=m['rows'], width=m['width'], offset=offset))
            offset += m['width']
        banks[mask] = dict(**bank, phase=group[0]['phase'], blocks=blocks)

    @lru_cache(None)
    def solve(mask):
        if mask == 0:
            return 0.0, ()
        first = mask & -mask
        sub = mask; best = (float('inf'), ())
        while sub:
            # Every partition has exactly one block containing its first item.
            if sub & first:
                rest, partition = solve(mask ^ sub)
                cost = banks[sub]['expected_bytes'] + rest
                if cost < best[0]:
                    best = cost, (sub,) + partition
            sub = (sub - 1) & mask
        return best
    cost, partition = solve((1 << len(members)) - 1)
    return cost, [banks[s] for s in partition]


def optimize(members, queries, degree_cap=joint.FIELD_DEGREE_CAP):
    assert members and {m['phase'] for m in members} <= {'source', 'auxiliary'}
    candidates = []
    for log_degree in range(max(m['rows'] for m in members).bit_length() - 1, degree_cap.bit_length()):
        cap = 1 << log_degree; banks = []
        for phase in ('source', 'auxiliary'):
            group = [m for m in members if m['phase'] == phase]
            if group:
                banks += best_partition(group, queries, cap)[1]
        degree = max(b['degree'] for b in banks)
        plan = joint.tree_plan(banks)
        cost = joint.opening_header(degree) + sum(joint.expected_tree(t['half'], t['leaf_bytes'], queries) for t in plan)
        candidates.append(dict(degree=degree, banks=banks, expected_opening_bytes=cost))
    return min(candidates, key=lambda c: c['expected_opening_bytes'])


def main():
    path = ROOT/'results/joint-nibble-geometry.json'
    original = json.loads(path.read_bytes())
    assert original['status'] == 'JOINT_NIBBLE_GEOMETRY_SCREEN_ONLY'
    for name, expected in original['sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected
    records = []
    for prior in original['scenarios']:
        members = [dict(table=i//2, phase='auxiliary' if i%2 else 'source', rows=b['rows'], width=b['width'])
                   for i, b in enumerate(prior['branches'])]
        best = optimize(members, prior['queries'])
        flat = [(b['phase'], m['table']) for b in best['banks'] for m in b['blocks']]
        assert len(flat) == len(set(flat)) == len(members)
        expected = prior['optimistic_fixed_bytes'] + best['expected_opening_bytes']
        assert expected <= prior['expected_optimistic_total_bytes'] + 1e-6
        totals = []
        for seed in range(16):
            rng = random.Random(18300 + seed)
            samples = [rng.randrange(4*best['degree']) for _ in range(prior['queries'])]
            payload = joint.count_payload(joint.tree_plan(best['banks']), samples)
            totals.append(prior['optimistic_fixed_bytes'] + joint.opening_header(best['degree']) + sum(
                t['leaves_bytes'] + t['siblings_bytes'] for t in payload))
        logical_cells = sum(m['rows']*m['width'] for m in members)
        bank_cells = sum(b['rows']*b['width'] for b in best['banks'])
        packed_cells = sum(b['degree']*b['lanes'] for b in best['banks'])
        records.append(dict(name=prior['name'], blocks=prior['blocks'], queries=prior['queries'], **best,
            bank_count=len(best['banks']), expected_optimistic_total_bytes=expected,
            separate_expected_bytes=prior['expected_optimistic_total_bytes'],
            expected_saving_bytes=prior['expected_optimistic_total_bytes']-expected,
            simulated_totals=totals, sampled_min_bytes=min(totals), sampled_max_bytes=max(totals),
            logical_base_cells=logical_cells, bank_base_cells=bank_cells,
            padded_packed_base_coefficients=packed_cells, packed_base_coefficient_payload_bytes=4*packed_cells,
            comparisons=[dict(component=c['component'], allowance_bytes=c['allowance_bytes'],
                expected_headroom_bytes=c['allowance_bytes']-expected) for c in prior['comparisons']],
            executable_profile=False, security_certified=False))
    sources = [Path(__file__), Path(joint.__file__), path,
               ROOT/'airbender/direct-wasm/ext8_pooled_weights.py',
               ROOT/'airbender/direct-wasm/ext8_commitment_profiles.py']
    report = dict(status='POOLED_JOINT_NIBBLE_GEOMETRY_ONLY', scenarios=records,
        assumptions=original['assumptions'] + [
            'Replace separate source/auxiliary trees with phase-separated banks of contiguous columns, padded to each bank maximum height.',
            'Exhaustive partition search within each 11-table phase; no cross-phase, row concatenation, new AIR or hash substitution.',
            'Logical root slots retained in execution header; static bank mapping and logical masked weights required but unimplemented for this 11-table profile.',
            'Packed base coefficient payload is a buffer size, not measured peak RAM; excludes Ext8 expansion, evaluations, Merkle trees, witnesses and scratch.'],
        decision='Do not implement enlarged pooled SHA proving solely for these results. Use exact bank groups and padded costs to assess whether pooling changes the byte decision. Failing expected/sampled scenarios do not rule out code switching, different AIR layouts, or algebraic hashing.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
    (ROOT/'results/pooled-joint-nibble-geometry.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps([{k:r[k] for k in ('name','queries','bank_count','expected_optimistic_total_bytes','expected_saving_bytes','sampled_min_bytes','sampled_max_bytes','packed_base_coefficient_payload_bytes')} for r in records],indent=2))


if __name__ == '__main__':
    main()
