"""Shadow-only exact response encoding census; never changes verifier hashes."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import struct
import sys
import time

import pq384_primitives as h
from measure_ext8_recursive_hash_work import frame
import measure_switch_verifier_work as workload

MAGIC = b'NPRSP001'


def encode(value):
    def put(v):
        if type(v) is int:
            assert 0 <= v < h.P
            return b'I' + struct.pack('<I', v)
        if type(v) is list:
            return b'L' + struct.pack('<I', len(v)) + b''.join(put(x) for x in v)
        assert type(v) is dict and set(v) in ({'leaf', 'path'}, {'values', 'path'})
        key = 'leaf' if 'leaf' in v else 'values'
        assert type(v['path']) is list
        digests = [bytes.fromhex(x) for x in v['path']]
        assert all(len(d) == 48 and d.hex() == x for d, x in zip(digests, v['path']))
        return (b'B' if key == 'leaf' else b'E') + put(v[key]) + struct.pack('<I', len(digests)) + b''.join(digests)
    return MAGIC + put(value)


def decode(wire):
    pos = 0
    def read(n):
        nonlocal pos
        if n < 0 or pos + n > len(wire): raise ValueError('truncated')
        data = wire[pos:pos+n]; pos += n
        return data
    def u32(): return struct.unpack('<I', read(4))[0]
    def get():
        tag = read(1)
        if tag == b'I':
            value = u32()
            if value >= h.P: raise ValueError('field word')
            return value
        if tag == b'L': return [get() for _ in range(u32())]
        if tag in (b'B', b'E'):
            value = get()
            return {'leaf' if tag == b'B' else 'values': value, 'path': [read(48).hex() for _ in range(u32())]}
        raise ValueError('tag')
    if read(len(MAGIC)) != MAGIC: raise ValueError('profile')
    result = get()
    if pos != len(wire) or encode(result) != wire: raise ValueError('noncanonical')
    return result


def measure(fn):
    rows = defaultdict(lambda: dict(calls=0, blocks=0, unique_calls=0, unique_blocks=0,
                                   candidate_blocks=0, candidate_unique_blocks=0))
    seen = set(); changed = set(); roundtrips = 0
    def profile(f, event, arg):
        nonlocal roundtrips
        if event != 'call' or f.f_code is not h.hash_parts.__code__: return
        tag, parts = f.f_locals['tag'], f.f_locals['parts']
        raw = frame(tag, parts); candidate = raw
        key = tag.decode()
        if tag == b'transcript/commit' and parts[1] == b'code-switch/source-responses':
            value = json.loads(parts[2]); encoded = encode(value)
            assert decode(encoded) == value
            roundtrips += 1
            candidate = frame(tag, (parts[0], parts[1], encoded))
            key += '/code-switch/source-responses'
        row = rows[key]
        blocks = (len(raw) + 144) // 128
        candidate_blocks = (len(candidate) + 144) // 128
        row['calls'] += 1; row['blocks'] += blocks; row['candidate_blocks'] += candidate_blocks
        if raw not in seen:
            seen.add(raw); row['unique_calls'] += 1; row['unique_blocks'] += blocks
        if candidate not in changed:
            changed.add(candidate); row['candidate_unique_blocks'] += candidate_blocks
    start = time.monotonic(); sys.setprofile(profile)
    try: result = fn()
    finally: sys.setprofile(None)
    assert result is True and roundtrips > 0
    keys = next(iter(rows.values())).keys()
    totals = {k: sum(r[k] for r in rows.values()) for k in keys}
    baseline = json.loads((workload.ROOT / 'results/switch-full-verifier-hash-work.json').read_text())
    assert all(totals[k] == v for k, v in baseline['measurement']['totals'].items())
    totals['unique_blocks_saved'] = totals['unique_blocks'] - totals['candidate_unique_blocks']
    return dict(tags=dict(rows), totals=totals, lossless_response_roundtrips=roundtrips,
                instrumented_seconds=time.monotonic()-start,
                candidate_scope='Frozen execution shadow: reencode response payloads only, keep original seeds and all other calls. A new protocol changes downstream challenges and needs fresh proofs. No measured proof-size or security improvement.',
                encoding_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == '__main__':
    workload.measure = measure
    workload.main()
