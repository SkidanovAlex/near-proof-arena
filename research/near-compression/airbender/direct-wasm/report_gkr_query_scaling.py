#!/usr/bin/env python3
"""Authenticated retained-tree size replay, not a secure high-query profile.
Reconstructs folded trees and counts actual zero-tagged source/extension words.
"""
import argparse
from array import array
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
import pq384_compact_gkr_bus_codec as codec
import pq384_global_chain as gc
from pq384_source_cache import SourceCache
from pq384_native_fft import NativeFFT
from pq384_cached_prover import FlatTree
from pq384_primitives import P


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fixture', type=Path, required=True)
    ap.add_argument('--fft-library', required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    statement = json.loads((a.fixture/'statement.json').read_text())
    proof = json.loads((a.fixture/'proof.json').read_text())
    provenance = json.loads((a.fixture/'prover-report.json').read_text())
    wire = (a.fixture/'proof.bin').read_bytes()
    spec, roots = statement['spec'], [bytes.fromhex(x) for x in statement['roots']]
    assert codec.decode(wire, spec, roots) == proof
    assert codec.encode(proof, spec, roots) == wire
    st, _, _, _, terminals, circuit, layout, binding, _, _ = codec.original.prefix(spec, roots, proof)
    obligation = codec.bus.gkr.verify(layout, binding, proof['gkr'])
    ars = [bytes.fromhex(x) for x in proof['aux_roots']]
    args = codec.bus.opening_arguments(spec, roots, ars, terminals, circuit, obligation)
    parent = codec.bus.opening_parent(binding, proof['gkr'])
    claim = obligation['private_claim']
    opening = proof['opening']
    joint = codec.compact.joint
    degrees, D, _, betas, fold_roots, contexts, challenges, _ = joint.replay(opening, st, parent, args, claim)
    native = NativeFFT(a.fft_library)
    paths = []
    for source, auxiliary in zip(provenance['source_cache_directories'], provenance['auxiliary_cache_directories']):
        paths.append(source)
        if auxiliary is not None:
            paths.append(auxiliary)
    with ExitStack() as stack:
        caches = [stack.enter_context(SourceCache(path, expected_root=bytes.fromhex(arg['root']),
                   log_rows=arg['log_rows'], width=arg['width'], packing=arg['packing'])) for path, arg in zip(paths, args)]
        assert len(caches) == len(args)
        combined = array('I', [0])*(4*D)
        for cache, beta in zip(caches, betas):
            words = joint.old.branch_words(cache, beta, D)
            for i, value in enumerate(words):
                combined[i] = (combined[i]+value) % P
        trees = []
        for challenge, root, ctx in zip(challenges, fold_roots, contexts):
            combined = native.fold_words(combined, challenge)
            tree = FlatTree(native.lde4_words(combined), ctx)
            assert tree.root == root, 'reconstructed fold commitment mismatch'
            trees.append(tree)
        cases = []
        original_queries = gc.QUERIES
        try:
            for queries in (8, 128, 239, 309, 463):
                gc.QUERIES = queries
                metadata = codec.compact.original.stages(opening, st, parent, args, claim)
                sections = []
                for j, (_, _, count, indices, words) in enumerate(metadata[:-1]):
                    tree = (caches+trees)[j]
                    out = codec.compact.Writer()
                    nonzero = zero = 0
                    for index in sorted(set(indices)):
                        values = tree.opening(index)['leaf']
                        assert len(values) == words
                        nonzero += sum(v != 0 for v in values)
                        zero += sum(v == 0 for v in values)
                        out.fields(values, True)
                    leaf_bytes = len(out.finish())
                    assert leaf_bytes == (nonzero*32+zero+7)//8
                    siblings = len(codec.compact.original.mp.boundary(count, indices))*48
                    sections.append({'kind': 'source' if j < len(caches) else 'fold', 'stage': j,
                                     'leaf_bytes': leaf_bytes, 'sibling_bytes': siblings,
                                     'zero_words': zero, 'nonzero_words': nonzero})
                cases.append({'queries': queries, 'sections': sections,
                              'opening_payload_bytes': sum(s['leaf_bytes']+s['sibling_bytes'] for s in sections)})
        finally:
            gc.QUERIES = original_queries
    fixed = len(wire)-cases[0]['opening_payload_bytes']
    opening_bytes = len(codec.compact.encode(opening, st, parent, args, claim))
    n = len(opening['rounds'])
    assert len(opening['reduction']) == n
    fixed_opening = 6+62*n+48*(n-1)+16
    assert opening_bytes-cases[0]['opening_payload_bytes'] == fixed_opening
    assert fixed == len(wire)-opening_bytes+fixed_opening
    transport = sum((a.fixture/f).stat().st_size for f in ('statement.json', 'request.json'))
    for c in cases:
        c['projected_proof_bytes'] = fixed+c['opening_payload_bytes']
        c['projected_current_transport_bytes'] = c['projected_proof_bytes']+transport
        c['source_payload_bytes'] = sum(s['leaf_bytes']+s['sibling_bytes'] for s in c['sections'] if s['kind']=='source')
        c['fold_payload_bytes'] = c['opening_payload_bytes']-c['source_payload_bytes']
    result = {'status': 'VERIFIED_Q8_AND_AUTHENTICATED_TREE_SIZE_REPLAY',
              'proof_sha256': hashlib.sha256(wire).hexdigest(), 'fixed_proof_bytes': fixed,
              'outer_gkr_and_local_bytes': len(wire)-opening_bytes, 'reconstructed_fold_roots': len(trees),
              'cases': cases, 'qualifications': ['Only Q8 is an actual verified profile. Larger query prefixes retain its domain separation; no secure profile is defined.',
                'Sizes include actual zero-tagged leaves authenticated against retained source roots and reconstructed fold roots.',
                'This supersedes full-word leaf estimates only for this retained compact diagnostic; sparsity is witness-dependent.',
                'Ext8 migration, soundness bounds, full NEAR scope and scaling remain open.']}
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
    for c in cases:
        print(c['queries'], c['projected_proof_bytes'], c['source_payload_bytes'], c['fold_payload_bytes'])


if __name__ == '__main__':
    main()
