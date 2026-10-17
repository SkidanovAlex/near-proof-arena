"""Witness-free joint SHA verifier cost screen; no new protocol/security claim.

Reconciles retained wire counts using real transcript-derived query indices.
Projects the SAME separate-tree weighted codec with optimistically frozen table
widths and zero GKR/routing/arithmetic costs. Expected bytes are not a universal
lower bound: this is one named architecture, with explicit lifted host caps.
"""
import gzip
import hashlib
import json
from pathlib import Path
import random

import pq384_ext8_auxiliary as aux
import pq384_ext8_weighted_codec as codec
import scheduled_bus_whir as algebra
from estimate_ext8_multiproof_geometry import frontier
from screen_weighted_code_switch import geometry

ROOT = Path(__file__).resolve().parents[2]
FIELD_DEGREE_CAP = 1 << 25  # Four-times LDE in BabyBear's 2^27 subgroup.


def branch(rows, width, packing):
    assert rows >= 2 and rows & (rows - 1) == 0
    assert packing > 0 and packing & (packing - 1) == 0
    degree = rows * packing
    assert degree <= FIELD_DEGREE_CAP
    lanes = (width + packing - 1) // packing
    return dict(rows=rows, width=width, packing=packing, degree=degree,
                lanes=lanes, half=2 * degree, leaf_bytes=8 * lanes)


def expected_tree(half, leaf_bytes, queries):
    leaves, siblings = geometry(half, queries)
    return leaf_bytes * leaves + 48 * siblings


def tree_plan(branches):
    degree = max(b['degree'] for b in branches)
    plan = [dict(kind='source', half=b['half'], leaf_bytes=b['leaf_bytes']) for b in branches]
    # Folded degree D/2 has D paired leaves; terminal constant tree is implicit.
    half = degree
    while half > 2:
        plan.append(dict(kind='fold', half=half, leaf_bytes=64))
        half //= 2
    return plan


def count_payload(plan, samples):
    rows = []
    for tree in plan:
        ids = {s % tree['half'] for s in samples}
        rows.append(dict(**tree, unique_leaves=len(ids), frontier_hashes=frontier(ids, tree['half']),
                         leaves_bytes=len(ids) * tree['leaf_bytes'],
                         siblings_bytes=48 * frontier(ids, tree['half'])))
    return rows


def opening_header(degree):
    return 8 + 240 * (degree.bit_length() - 1) + 32


def optimize_packings(rows, widths, queries, degree_cap=FIELD_DEGREE_CAP):
    """Exact finite expected-cost search within this frozen, separate-tree shape.

    Conditional on a max degree, branch costs separate. Enumerate power-of-two
    packings only up to the first that gives one lane (larger ones cannot improve
    this model); enumerate every possible max degree up to the field cap.
    """
    assert len(rows) == len(widths) and rows and all(w > 0 for w in widths)
    assert max(rows) <= degree_cap <= FIELD_DEGREE_CAP and degree_cap & (degree_cap - 1) == 0
    candidates = []
    for log_degree in range(max(rows).bit_length() - 1, degree_cap.bit_length()):
        cap = 1 << log_degree
        chosen = []
        for n, w in zip(rows, widths):
            options = []
            for log_packing in range(min(log_degree - (n.bit_length() - 1), (w - 1).bit_length()) + 1):
                b = branch(n, w, 1 << log_packing)
                b['expected_bytes'] = expected_tree(b['half'], b['leaf_bytes'], queries)
                options.append(b)
            chosen.append(min(options, key=lambda b: b['expected_bytes']))
        actual = max(b['degree'] for b in chosen)
        plan = tree_plan(chosen)
        cost = opening_header(actual) + sum(expected_tree(t['half'], t['leaf_bytes'], queries) for t in plan)
        candidates.append(dict(degree=actual, searched_degree_cap=cap, branches=chosen,
                               expected_opening_bytes=cost))
    return min(candidates, key=lambda c: c['expected_opening_bytes'])


def main():
    paths = [
        'results/sha384-nibble64/statement.json.gz', 'results/sha384-nibble64/reduction.json.gz',
        'results/sha384-nibble64/opening.json.gz', 'results/sha384-nibble64/proof.json.gz',
        'results/sha384-nibble64/codec-report.json', 'results/sha384-nibble64/compression.bin',
        'results/sha384-nibble64/prover-report.json', 'results/switch-full-verifier-hash-work.json',
        'results/closed-hybrid-work.json', 'results/derived-transcript-bindings.json',
        'results/nibble-full-verifier-screen.json']
    def read(name):
        raw = (ROOT / name).read_bytes()
        return json.loads(gzip.decompress(raw) if name.endswith('.gz') else raw)
    statement, reduction, opening, proof, measured = map(read, paths[:5])
    spec = statement['spec']; tables = spec['air']['tables']
    branches = []
    for ti, table in enumerate(tables):
        for width, packing in [(table['width'], spec['source_packings'][ti]),
                               (8 * aux.layout(table)['aux_columns'], spec['aux_packings'][ti])]:
            branches.append(branch(1 << spec['log_rows'][ti], width, packing))
    assert len(branches) == len(opening['branches'])
    for b, descriptor in zip(branches, opening['branches']):
        assert (b['rows'], b['width'], b['packing']) == (1 << descriptor['log_rows'], descriptor['width'], descriptor['packing'])
    real_plan, samples, _ = codec.stages(proof, bytes.fromhex(opening['statement']),
        bytes.fromhex(opening['parent']), opening['branches'], opening['claim'], opening['queries'])
    plan = tree_plan(branches)
    assert [(t['half'], t['leaf_bytes']) for t in plan] == [(t['half'], t['width']) for t in real_plan]
    payload = count_payload(plan, samples)
    components = dict(execution_header_and_roots=8 + 96 * len(tables),
        finals=32 * sum(aux.layout(t)['finals'] for t in tables),
        local=32 * sum(n * (algebra.table_degree(t, 0) + 2) for n, t in zip(spec['log_rows'], tables)),
        gkr=32 * sum(sum(len(r) for r in layer['rounds']) + len(layer['inputs']) for layer in reduction['gkr']['layers']),
        opening_header=opening_header(max(b['degree'] for b in branches)),
        opening_leaves=sum(t['leaves_bytes'] for t in payload),
        opening_siblings=sum(t['siblings_bytes'] for t in payload))
    assert components['opening_header'] + components['opening_leaves'] + components['opening_siblings'] == measured['opening_bytes']
    wire = (ROOT / paths[5]).read_bytes()
    assert sum(components.values()) == len(wire) == measured['proof_bytes'] == 265040
    assert hashlib.sha256(wire).hexdigest() == measured['proof_sha256']
    # Check each nonopening byte against the independently retained messages.
    vector = codec.p.vector_bytes
    prefix = b'NPEX8002' + b''.join(bytes.fromhex(r) for r in statement['roots'] + reduction['aux_roots'])
    prefix += b''.join(vector(fs) for fs in reduction['finals'])
    prefix += b''.join(vector(r) for table in reduction['local'] for r in table)
    prefix += b''.join(b''.join(vector(r) for r in layer['rounds']) + vector(layer['inputs']) for layer in reduction['gkr']['layers'])
    assert wire[:len(prefix)] == prefix and len(prefix) == measured['nonopening_bytes']

    work, hybrid, derived, bounds = map(read, paths[7:])
    scenarios = []
    for label, blocks in [('measured_full_verifier', work['measurement']['totals']['unique_blocks']),
        ('closed_stage_binding_counterfactual', hybrid['unchanged_other_work_counterfactual_blocks']),
        ('prior_optimistic_hash_erasure', derived['optimistic_hash_screen']['remaining_unique_blocks'])]:
        logs = list(spec['log_rows'])
        for ti, per_block in [(0, 64), (1, 80), (2, 1), (10, 1)]:
            logs[ti] = (blocks * per_block - 1).bit_length()
        row_counts = [1 << n for n in logs for _ in range(2)]
        widths = [b['width'] for b in branches]
        fixed = components['execution_header_and_roots'] + components['finals'] + 32 * sum(
            n * (algebra.table_degree(t, 0) + 2) for n, t in zip(logs, tables))
        for queries in (8, 309):
            best = optimize_packings(row_counts, widths, queries)
            plan = tree_plan(best['branches']); trials = []
            for seed in range(16):
                rng = random.Random(17300 + seed)
                payload = count_payload(plan, [rng.randrange(4 * best['degree']) for _ in range(queries)])
                trials.append(fixed + opening_header(best['degree']) + sum(t['leaves_bytes'] + t['siblings_bytes'] for t in payload))
            expected = fixed + best['expected_opening_bytes']
            scenarios.append(dict(name=label, blocks=blocks, queries=queries, table_log_rows=logs,
                optimistic_fixed_bytes=fixed, **best, expected_optimistic_total_bytes=expected,
                sampled_min_bytes=min(trials), sampled_max_bytes=max(trials), simulated_totals=trials,
                comparisons=[dict(component=r['component'], allowance_bytes=r['allowance_bytes'],
                    expected_headroom_bytes=r['allowance_bytes']-expected) for r in bounds['replacement_comparisons']],
                within_current_degree_cap=all(b['degree'] <= 1 << 18 for b in best['branches']),
                within_current_lane_cap=all(b['lanes'] <= 64 for b in best['branches']),
                security_certified=False, executable_profile=False))
    report = dict(status='JOINT_NIBBLE_GEOMETRY_SCREEN_ONLY', baseline=dict(
        proof_bytes=len(wire), components=components, transcript_samples=samples,
        nonopening_byte_equality=True, transcript_derived_opening_geometry=True), scenarios=scenarios,
        assumptions=['Single joint envelope, 22 separate source/auxiliary trees, existing rate4 weighted folding codec.',
            'Retain baseline widths and finals; multiplicity growth is priced at zero. New constraints and GKR priced at zero.',
            'Hash call routing, message framing/chaining, verifier arithmetic, challenge derivation and application binding priced at zero.',
            'Uniform-with-replacement query model; expected costs and 16 seeded simulations are not worst-case bounds.',
            'Lift implementation degree2^18 and lane64 caps, retain BabyBear subgroup/rate4 degree2^25 cap.',
            'q8 and q309 are sensitivity scenarios, neither certifies PQ128. Old workloads do not measure a redesigned transcript.'],
        decision='This screen prices a named joint SHA architecture before witness generation. Expected/sampled budget failures reject this candidate for further scale-up at these packings, not all joint/pooled/code-switch/algebraic-hash protocols. An algebraic-hash candidate still needs its own table layout and security assumptions; S-box counts do not determine outer bytes.',
        missing=['Full joint relation/compiler and valid enlarged multiplicity bounds', 'Complete GKR/routing/arithmetic byte model',
            'Concrete outer security ledger and adaptive QROM soundness', 'Full NEAR semantics and 1 Petagas capacity'],
        sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                [Path(__file__), Path(codec.__file__), Path(codec.p.__file__), Path(aux.__file__), Path(algebra.__file__),
                 ROOT/'airbender/direct-wasm/ext8_execution_codec.py',
                 ROOT/'airbender/direct-wasm/packed_claim_handoff.py',
                 ROOT/'airbender/direct-wasm/pq384_ext8_weight_families.py',
                 ROOT/'airbender/direct-wasm/sha384_nibble_phase_air.py',
                 ROOT/'airbender/direct-wasm/sha384_nibble_boundary_air.py',
                 ROOT/'airbender/direct-wasm/screen_weighted_code_switch.py',
                 ROOT/'airbender/direct-wasm/estimate_ext8_multiproof_geometry.py'] + [ROOT/n for n in paths]})
    target=ROOT/'results/joint-nibble-geometry.json'; target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(baseline=report['baseline'], scenarios=[{k:r[k] for k in
        ('name','blocks','queries','degree','expected_optimistic_total_bytes','sampled_min_bytes','sampled_max_bytes','within_current_degree_cap','within_current_lane_cap')} for r in scenarios]),indent=2))


if __name__ == '__main__':
    main()
