"""Exhaustive small-tree/packing checks independent of the large projection."""
import itertools
import json
import math
from pathlib import Path
import model_joint_nibble_geometry as m


def main():
    cases = 0
    for rows, widths in [([2, 4], [3, 9]), ([4, 8], [1, 7]), ([2, 2, 4], [2, 5, 3])]:
        for q in (1, 3, 8):
            choices = [[m.branch(n, w, 1 << k) for k in range((w - 1).bit_length() + 1)
                        if n * (1 << k) <= 32] for n, w in zip(rows, widths)]
            expected = min(m.opening_header(max(b['degree'] for b in bs)) + sum(
                m.expected_tree(t['half'], t['leaf_bytes'], q) for t in m.tree_plan(bs))
                for bs in itertools.product(*choices))
            actual = m.optimize_packings(rows, widths, q, degree_cap=32)
            assert math.isclose(actual['expected_opening_bytes'], expected, abs_tol=1e-8)
            cases += 1
    plan = m.tree_plan([m.branch(2, 3, 2), m.branch(4, 2, 1)])
    exhaustive = 0
    for q in (1, 2, 3):
        sums = []
        for samples in itertools.product(range(16), repeat=q):
            sizes = m.count_payload(plan, samples)
            sums.append(sum(t['leaves_bytes'] + t['siblings_bytes'] for t in sizes))
            exhaustive += 1
        expected = sum(m.expected_tree(t['half'], t['leaf_bytes'], q) for t in plan)
        assert math.isclose(sum(sums)/len(sums), expected, abs_tol=1e-8)
    rejected = 0
    for action in [lambda: m.branch(1 << 25, 3, 2),
                   lambda: m.optimize_packings([2, 4], [3], 8),
                   lambda: m.optimize_packings([64], [3], 8, degree_cap=32)]:
        try: action()
        except AssertionError: rejected += 1
        else: raise AssertionError('invalid geometry accepted')
    print(json.dumps(dict(status='PASS', exhaustive_packing_cases=cases,
        joint_query_sequences=exhaustive, invalid_geometry_rejections=rejected,
        scope='Cost arithmetic, optimizer and finite uniform-query geometry only; no soundness claim.')))


if __name__ == '__main__':
    main()
