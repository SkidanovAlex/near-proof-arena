"""Audit captured hashing and isolate layout-hash cost; no transcript conversion."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import struct

from pq384_primitives import PREFIX


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--capture', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    calls_path = args.capture / 'hash-calls.json'
    events_path = args.capture / 'hash-occurrences.json'
    calls = json.loads(calls_path.read_text())
    events = json.loads(events_path.read_text())
    counts = Counter()
    for component, index in events:
        if type(component) is not int or component < 0 or type(index) is not int or not 0 <= index < len(calls):
            raise ValueError('invalid occurrence')
        counts[index] += 1
    if set(counts) != set(range(len(calls))):
        raise ValueError('unreferenced captured hash')
    total = 0
    layouts = []
    for index, call in enumerate(calls):
        tag = bytes.fromhex(call['tag_hex'])
        parts = [bytes.fromhex(p) for p in call['parts_hex']]
        framed = (PREFIX + struct.pack('<I', len(tag)) + tag + struct.pack('<I', len(parts))
                  + b''.join(struct.pack('<Q', len(p)) + p for p in parts))
        if hashlib.sha384(framed).hexdigest() != call['digest_hex']:
            raise ValueError('captured hash mismatch')
        blocks = (len(framed) + 17 + 127) // 128
        total += counts[index] * blocks
        if tag == b'near-pq384-terminal-gkr-v1' and len(parts) == 1:
            layout = json.loads(parts[0])
            canonical = json.dumps(layout, sort_keys=True, separators=(',', ':')).encode()
            if canonical != parts[0]:
                raise ValueError('noncanonical layout')
            layouts.append(dict(index=index, bytes=len(parts[0]), occurrences=counts[index],
                                blocks_per_call=blocks, blocks=counts[index]*blocks,
                                layers=len(layout['layers']), input_size=layout['input_size']))
    if not layouts:
        raise ValueError('no layout hashes')
    removed = sum(row['blocks'] for row in layouts)
    report = dict(status='PASS', checked_distinct_hash_calls=len(calls), occurrences=len(events),
                  total_compression_blocks=total, layout_hashes=layouts,
                  layout_compression_blocks=removed, layout_fraction=removed/total,
                  remaining_blocks_if_only_layout_hashes_removed=total-removed,
                  files={str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in (calls_path, events_path, Path(__file__))},
                  requirements=[
                      'Fix canonical AIR digest and compiler semantics in trusted verifier configuration.',
                      'Derive layout from bound statement, challenges, finals and terminal claims; never accept a prover-selected layout.',
                      'Version the transcript and regenerate proofs; old proof bytes cannot be reused.',
                      'Bind derived input weights and final GKR seed to the PCS handoff.'],
                  limits=[
                      'Subtraction is isolated cost accounting, not a measured migrated verifier or security equivalence.',
                      'Other transcript calls, arithmetic, Merkle paths and parsing still need recursive constraints.',
                      'Occurrences count replay work; this is not unique full-state node accounting.',
                      'No outer proof, proof-size prediction, or quantum-security conclusion.'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('status','total_compression_blocks','layout_compression_blocks','remaining_blocks_if_only_layout_hashes_removed')}))


if __name__ == '__main__':
    main()
