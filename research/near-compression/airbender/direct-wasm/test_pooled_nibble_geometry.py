"""Compare subset DP against independent enumeration of all small partitions."""
import itertools
import json
import math
import model_pooled_nibble_geometry as m


def partitions(items):
    if not items:
        yield []
        return
    first, *rest = items
    for groups in partitions(rest):
        yield [[first]] + groups
        for i in range(len(groups)):
            yield groups[:i] + [[first] + groups[i]] + groups[i+1:]


def brute(members, queries, cap):
    phase_partitions = [list(partitions([x for x in members if x['phase'] == phase]))
                        for phase in ('source', 'auxiliary')]
    best = float('inf'); checked = 0
    for groups_by_phase in itertools.product(*phase_partitions):
        groups = [g for gs in groups_by_phase for g in gs]
        options = []
        for g in groups:
            rows = max(x['rows'] for x in g); width = sum(x['width'] for x in g)
            options.append([m.joint.branch(rows, width, 1 << k) for k in range((width-1).bit_length()+1)
                            if rows * (1 << k) <= cap])
        for banks in itertools.product(*options):
            degree = max(b['degree'] for b in banks)
            cost = m.joint.opening_header(degree) + sum(m.joint.expected_tree(t['half'], t['leaf_bytes'], queries)
                                                       for t in m.joint.tree_plan(banks))
            best = min(best, cost); checked += 1
    return best, checked


def main():
    total = cases = 0
    for shape in [((2, 3), (4, 7), (2, 2)), ((2, 1), (2, 3), (4, 2), (4, 3))]:
        for split in (False, True):
            members = [dict(table=i, rows=n, width=w, phase='auxiliary' if split and i%2 else 'source')
                       for i, (n, w) in enumerate(shape)]
            for q in (1, 8, 31):
                expected, count = brute(members, q, 32)
                actual = m.optimize(members, q, degree_cap=32)
                assert math.isclose(expected, actual['expected_opening_bytes'], abs_tol=1e-8)
                seen = []
                for bank in actual['banks']:
                    assert sum(b['width'] for b in bank['blocks']) == bank['width']
                    assert max(b['rows'] for b in bank['blocks']) == bank['rows']
                    offset = 0
                    for block in bank['blocks']:
                        assert block['offset'] == offset
                        assert members[block['table']]['phase'] == bank['phase']
                        seen.append(block['table']); offset += block['width']
                assert sorted(seen) == list(range(len(members)))
                total += count; cases += 1
    bad = [dict(table=0, rows=2, width=3, phase='source'),
           dict(table=1, rows=2, width=3, phase='auxiliary')]
    try:
        m.best_partition(bad, 8, 32)
    except AssertionError:
        pass
    else:
        raise AssertionError('source/auxiliary commitment timing mixed')
    print(json.dumps(dict(status='PASS', exhaustive_cases=cases, enumerated_partition_packing_choices=total,
        cross_phase_merge_rejected=True, coverage_offsets_checked=True,
        scope='Finite expected-cost optimization and layout coverage only; no proof profile or soundness certification.')))


if __name__ == '__main__':
    main()
