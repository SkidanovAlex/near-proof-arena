#!/usr/bin/env python3
"""Exploratory block commitments, NOT the formally connected Wasm page scheme.

Reuses the verified-by-rebuild Python harness, not Lean's page proofs. Leaf size
is domain-bound. Initial layout/count/root are trusted; no proof-system claims.
"""
import argparse
import hashlib
import json
import platform
import random
import ssl
import time
from pathlib import Path
import memory_batch_bench as bench


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repetitions', type=int, default=3)
    args = parser.parse_args()
    assert args.repetitions > 0
    memory_size = 8 * 1024 * 1024
    memory = bytes(range(256)) * (memory_size // 256)
    rng = random.Random(20261015)
    sparse = [(rng.randrange(memory_size), rng.randrange(256)) for _ in range(16)]
    # Requests are identical for every leaf size. Contiguous workloads are also
    # sensitive to the deliberately unaligned start; no reordering is done.
    cases = [('single_byte', [(17, 7)]), ('sparse_16', sparse)]
    for name, start, size in [('contiguous_4k', 17, 4096),
                              ('cross_wasm_page_4k', 65536 - 1024, 4096),
                              ('contiguous_64k', 0, 65536)]:
        cases.append((name, [(start + i, (i * 31 + 7) % 256) for i in range(size)]))
    results, mutation_checks, construction = [], [], []
    for block in [256, 1024, 4096, 65536]:
        bench.PAGE = block
        # These roots are deliberately a different protocol from PageTree.lean.
        bench.LEAF = b'nearproof-block-v1' + block.to_bytes(4, 'little')
        bench.NODE = b'nearproof-block-node-v1' + block.to_bytes(4, 'little')
        depth = (memory_size // block).bit_length() - 1
        started = time.perf_counter()
        tree = bench.CachedTree(memory)
        construction.append(dict(block_bytes=block, seconds=time.perf_counter()-started,
                                 root=tree.tree[1].hex(), leaf_count=tree.count, depth=depth))
        mutation_checks.append(dict(block_bytes=block, rejected=bench.negative_tests(memory)))
        for name, requests in cases:
            runs = []
            for repetition in range(args.repetitions):
                result = bench.run(memory, requests, True)
                result.update(case=name, block_bytes=block, depth=depth, repetition=repetition)
                runs.append(result)
            assert len({r['final_root'] for r in runs}) == 1
            results.extend(runs)
            print(block, name, runs[0]['batches'], runs[0]['witness_bytes_excluding_shared_descriptor'], flush=True)
    sources = [Path(__file__), Path(bench.__file__)]
    report = dict(kind='experimental_block_leaf_sweep_not_lean_refinement_or_succinct_proof',
                  memory_bytes=memory_size, repetitions=args.repetitions,
                  python=platform.python_version(), platform=platform.platform(), openssl=ssl.OPENSSL_VERSION,
                  sources={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
                  request_sha256={name: hashlib.sha256(b''.join(a.to_bytes(8, 'little')+bytes([v])
                                     for a,v in requests)).hexdigest() for name,requests in cases},
                  construction=construction, mutation_checks=mutation_checks, results=results,
                  limitations=['Different commitment protocol from current Lean page trees',
                               'No subpage-to-Wasm refinement proof yet',
                               'Trusts initial layout/count/root; no quantum-security assertion',
                               'Witness transport includes explicit update records; not succinct proof bytes',
                               'Update timings exclude construction/grouping/materialization',
                               'Shared-host Python/SHA-512 timings do not predict AIR/prover cost'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
