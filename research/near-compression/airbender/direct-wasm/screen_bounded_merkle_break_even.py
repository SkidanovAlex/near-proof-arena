"""Optimistic byte-floor falsification for the existing bounded Merkle codec.

Not a cryptographic lower bound or a proof of soundness. Batching is hypothetical:
we grant perfect hash sharing but retain this codec and 25-block chunk capacity.
"""
import gzip
import hashlib
import json
from pathlib import Path

import merkle_recursive_call_routes as route
import private_merkle_proof as proof

ROOT = Path(__file__).resolve().parents[2]


def frontier(depth, mask):
    """Union of paths from selected public leaves; count external sibling nodes."""
    selected = {i for i in range(1 << depth) if mask >> i & 1}
    assert selected
    active = selected
    nodes = external = 0
    for _ in range(depth):
        parents = {i // 2 for i in active}
        external += sum((i ^ 1) not in active for i in active)
        nodes += len(parents)
        active = parents
    assert active == {0}
    # Each computed parent has one or two computed children. Only the former
    # introduces an external sibling. Hence external <= computed parents.
    assert external <= nodes
    return len(selected), nodes, external


def build():
    capture = ROOT / 'results/private-merkle-proof-q8'
    public = json.loads((capture / 'public.json').read_text())
    spec = json.loads(gzip.decompress((capture / 'trusted-spec.json.gz').read_bytes()))
    wire = (capture / 'proof.bin').read_bytes()
    assert len(bytes.fromhex(public['context_hex'])) == 197
    tables = len(spec['air']['tables'])
    assert tables == 4
    outer = len(proof.BUNDLE_MAGIC) + len(route.u64(0))
    compression_header = len(proof.compression.magic('affine-v1', 'separate')) + 2 * tables * 48
    routing_header = len(proof.ROUTE_MAGIC)
    floor = outer + compression_header + routing_header
    assert wire[:8] == proof.BUNDLE_MAGIC
    compression_length = int.from_bytes(wire[8:16], 'little')
    assert wire[16:24] == proof.compression.magic('affine-v1', 'separate')
    assert wire[16 + compression_length:24 + compression_length] == proof.ROUTE_MAGIC
    assert floor == 416
    cases = []
    node_cost = None
    for depth in range(1, 5):
        statement = dict(public, leaf_count=1 << depth)
        program = route.compile_routes(statement)
        costs = [(c['tag'], len(c['rows'])) for c in program['calls']]
        node_costs = {n for tag, n in costs if tag == 'merkle/node'}
        assert node_costs == {4}
        node_cost = node_costs.pop()
        assert program['use_count'] == 6 + 4 * depth <= 25
        assert len(program['private_pairs']) * 2 == 48 * depth
        cases.append(dict(depth=depth, compression_blocks=program['use_count'],
                          sibling_bytes=48 * depth, optimistic_wire_floor=floor,
                          breaks_even=floor < 48 * depth))
    batch_cases = feasible = max_frontier = 0
    for depth in range(1, 5):
        for mask in range(1, 1 << (1 << depth)):
            leaves, nodes, external = frontier(depth, mask)
            batch_cases += 1
            # All selected leaves public; one tree/context and one root wrapper.
            blocks = 3 * leaves + node_cost * nodes + 3
            if blocks <= 25:
                feasible += 1
                max_frontier = max(max_frontier, 48 * external)
    optimistic_nodes = 25 // node_cost  # Deliberately omit leaf/root cost.
    optimistic_frontier = 48 * optimistic_nodes
    assert max_frontier <= optimistic_frontier < floor
    files = [Path(__file__), Path(route.__file__), Path(proof.__file__),
             Path(proof.compression.__file__), capture / 'public.json',
             capture / 'trusted-spec.json.gz', capture / 'proof.bin']
    return dict(
        status='BOUNDED_ARCHITECTURE_NO_BREAK_EVEN',
        security_status='NOT_PASSED',
        scope='Existing separate-root codec, at most 25 SHA384 blocks, 197-byte context; public leaves; compare deduplicated sibling frontier only.',
        excluded='Not full recursive PCS, arbitrary verifier witnesses, changed codecs, larger chunks, or other hash framing. No quantum-security or Lean correctness claim.',
        context_bytes=len(bytes.fromhex(public['context_hex'])),
        mandatory_bytes=dict(outer=outer, compression=compression_header,
                             routing=routing_header, total=floor),
        single_path_cases=cases,
        hypothetical_batch=dict(implemented=False, exhaustive_subsets=batch_cases,
                                subsets_within_capacity=feasible,
                                maximum_frontier_bytes_within_capacity=max_frontier,
                                conservative_node_budget=optimistic_nodes,
                                conservative_frontier_bytes=optimistic_frontier,
                                justification='Each computed parent along a union of paths has at least one computed child, so at most one external sibling. Every such parent costs four compression blocks. Leaf/root work is omitted in the conservative bound.'),
        decision='Do not generate larger proofs in this bounded profile to seek compression. A next experiment must change capacity/codec or prove a larger verifier workload, and pass an optimistic complete-byte screen before formalization.',
        source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files})


if __name__ == '__main__':
    print(json.dumps(build(), indent=2, sort_keys=True))
