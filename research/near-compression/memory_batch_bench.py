#!/usr/bin/env python3
"""SHA-512 memory-authentication microbenchmark; not a proof-system benchmark.

Page/node messages match PageCommitment.lean and PageTree.lean. Python execution
is not proved equivalent to Lean. Witness byte accounting is a proposed local
transport, not the whole-state codec or a succinct proof. No security claim.
"""
import argparse
import hashlib
import json
import platform
import ssl
import time
from pathlib import Path

PAGE = 65536
LEAF = b'nearproof-page-v1'
NODE = b'nearproof-node-v1'


def blob(b):
    return len(b).to_bytes(4, 'little') + b


class Hashes:
    def __init__(self):
        self.calls = self.bytes = 0

    def __call__(self, b):
        self.calls += 1
        self.bytes += len(b)
        return hashlib.sha512(b).digest()


def leaf(h, page):
    return h(LEAF + blob(page))


def node(h, left, right):
    return h(NODE + blob(left) + blob(right))


def full_root(memory):
    """Independent bottom-up rebuild from flat, directly updated memory."""
    h = lambda b: hashlib.sha512(b).digest()
    layer = [leaf(h, memory[i:i + PAGE]) for i in range(0, len(memory), PAGE)]
    while len(layer) > 1:
        layer = [node(h, layer[i], layer[i + 1]) for i in range(0, len(layer), 2)]
    return layer[0]


class CachedTree:
    def __init__(self, memory):
        self.pages = [bytes(memory[i:i + PAGE]) for i in range(0, len(memory), PAGE)]
        self.count = len(self.pages)
        assert self.count and self.count & (self.count - 1) == 0
        self.depth = self.count.bit_length() - 1
        self.h = Hashes()
        self.tree = [b''] * (2 * self.count)
        for i, page in enumerate(self.pages):
            self.tree[self.count + i] = leaf(self.h, page)
        for i in range(self.count - 1, 0, -1):
            self.tree[i] = node(self.h, self.tree[2*i], self.tree[2*i+1])
        self.h = Hashes()  # exclude construction from update measurements

    def opening(self, index):
        i, siblings = self.count + index, []
        while i > 1:
            siblings.append(self.tree[i ^ 1])
            i //= 2
        return self.pages[index], siblings  # leaf-to-root internally

    def update(self, index, page):
        self.pages[index] = bytes(page)
        i = self.count + index
        self.tree[i] = leaf(self.h, self.pages[index])
        while i > 1:
            i //= 2
            self.tree[i] = node(self.h, self.tree[2*i], self.tree[2*i+1])


def path_root(h, count, index, page, siblings):
    if not 0 <= index < count or len(page) != PAGE:
        raise ValueError('allocation/page size')
    if count <= 0 or count & (count - 1) or len(siblings) != count.bit_length() - 1:
        raise ValueError('shape')
    value = leaf(h, page)
    for sibling in siblings:
        if len(sibling) != 64:
            raise ValueError('digest size')
        value = node(h, sibling, value) if index & 1 else node(h, value, sibling)
        index //= 2
    return value


def verify_update(h, root, count, index, old_page, siblings, writes, expected):
    if [(index * PAGE + offset, value) for offset, value in writes] != expected:
        raise ValueError('request sequence')
    if any(not 0 <= offset < PAGE or not 0 <= value < 256 for offset, value in writes):
        raise ValueError('write bounds')
    if path_root(h, count, index, old_page, siblings) != root:
        raise ValueError('old root')
    new_page = bytearray(old_page)
    for offset, value in writes:
        new_page[offset] = value
    return path_root(h, count, index, new_page, siblings)


def group_requests(requests, batch):
    groups = []
    for address, value in requests:
        index, offset = divmod(address, PAGE)
        if not batch or not groups or groups[-1][0] != index:
            groups.append((index, []))
        groups[-1][1].append((offset, value))
    return groups


def run(memory, requests, batch):
    tree = CachedTree(memory)
    root, verifier = tree.tree[1], Hashes()
    groups = group_requests(requests, batch)
    cursor = wire = 0
    generate_seconds = verify_seconds = 0.0
    for index, writes in groups:
        start = time.perf_counter()
        page, siblings = tree.opening(index)
        new_page = bytearray(page)
        for offset, value in writes:
            new_page[offset] = value
        tree.update(index, new_page)
        generate_seconds += time.perf_counter() - start
        start = time.perf_counter()
        root = verify_update(verifier, root, tree.count, index, page, siblings,
                             writes, requests[cursor:cursor + len(writes)])
        verify_seconds += time.perf_counter() - start
        cursor += len(writes)
        # index u64, page blob, path length u32, (direction u8 + digest blob),
        # writes length u32, (offset u32 + byte). Shared descriptor excluded.
        wire += 8 + 4 + len(page) + 4 + len(siblings) * 69 + 4 + len(writes) * 5
        assert root == tree.tree[1]
    direct = bytearray(memory)
    for address, value in requests:
        direct[address] = value
    assert cursor == len(requests)
    assert b''.join(tree.pages) == direct
    assert root == full_root(direct)
    return dict(mode='page_batch' if batch else 'per_byte', writes=len(requests), batches=len(groups),
                witness_bytes_excluding_shared_descriptor=wire,
                producer_hash_calls=tree.h.calls, producer_hash_input_bytes=tree.h.bytes,
                verifier_hash_calls=verifier.calls, verifier_hash_input_bytes=verifier.bytes,
                producer_update_seconds=generate_seconds, verifier_seconds=verify_seconds,
                final_root=root.hex(), independent_rebuild_matches=True)


def negative_tests(memory):
    tree = CachedTree(memory)
    page, siblings = tree.opening(0)
    writes, expected = [(1, 7), (2, 9)], [(1, 7), (2, 9)]
    base = [tree.tree[1], tree.count, 0, page, siblings, writes, expected]
    cases = {}
    cases['page'] = {3: bytes([page[0] ^ 1]) + page[1:]}
    cases['sibling'] = {4: [bytes([siblings[0][0] ^ 1]) + siblings[0][1:]] + siblings[1:]}
    cases['root'] = {0: b'\x00' * 64}
    cases['path_length'] = {4: siblings[:-1]}
    cases['reordered_writes'] = {5: list(reversed(writes))}
    cases['changed_value'] = {5: [(1, 8), (2, 9)]}
    cases['missing_write'] = {5: writes[:1]}
    cases['duplicate_write'] = {5: writes + writes[:1]}
    cases['stale_opening'] = {0: verify_update(Hashes(), *base)}
    cases['allocation'] = {2: tree.count, 6: [(tree.count * PAGE + o, v) for o, v in writes]}
    for name, changes in cases.items():
        args = list(base)
        for index, value in changes.items():
            args[index] = value
        try:
            verify_update(Hashes(), *args)
        except ValueError:
            continue
        raise AssertionError(f'mutation accepted: {name}')
    return list(cases)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    # Fixed 8 MiB, 128-page memory; deterministic nonzero contents.
    memory = bytes(range(256)) * (128 * PAGE // 256)
    cases = [('one_byte', 17, 1, True), ('same_page_256', 17, 256, True),
             ('same_page_4096', 17, 4096, True), ('cross_page_4096', PAGE - 1024, 4096, True),
             ('multi_page_1mib', PAGE - 1024, 1 << 20, False)]
    results = []
    for name, address, size, baseline in cases:
        requests = [(address + i, (i * 31 + 7) % 256) for i in range(size)]
        for batch in ([False, True] if baseline else [True]):
            result = run(memory, requests, batch)
            result['case'] = name
            results.append(result)
            print(name, result['mode'], result['batches'], result['verifier_seconds'], flush=True)
    report = dict(kind='memory_authentication_microbenchmark_not_succinct_proof',
                  python=platform.python_version(), platform=platform.platform(), openssl=ssl.OPENSSL_VERSION,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  page_bytes=PAGE, page_count=128, depth=7,
                  construction_and_grouping_excluded_from_timings=True,
                  repetitions=1, rejected_mutations=negative_tests(memory), results=results,
                  limitations=['Not an AIR/prover benchmark or quantum security proof',
                               'Python-to-Lean equivalence is not proved',
                               'Initial count/depth/root are trusted; descriptor authentication is not timed',
                               'Proposed witness transport; not final proof bytes',
                               'Single-run timings on a shared host; grouping/materialization excluded',
                               'Baseline omitted for 1 MiB to bound work'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
