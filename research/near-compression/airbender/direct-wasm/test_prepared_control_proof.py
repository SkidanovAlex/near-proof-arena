"""Binary and statement binding checks for an already generated control proof."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import pq384_global_bus as bus
import pq384_global_bus_codec as codec


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--proof-dir', type=Path, required=True)
    p.add_argument('--canonical-spec', type=Path, required=True)
    a = p.parse_args()
    statement = json.loads((a.proof_dir/'statement.json').read_text())
    original = json.loads(a.canonical_spec.read_text())
    for key in ('air', 'public', 'log_rows'):
        assert statement['spec'][key] == original[key]
    proof = json.loads((a.proof_dir/'proof.json').read_text())
    spec = statement['spec']
    roots = [bytes.fromhex(r) for r in statement['roots']]
    assert bus.verify(proof, spec, roots)
    wire = codec.encode(proof, spec, roots)
    assert codec.decode(wire, spec, roots) == proof
    (a.proof_dir/'proof.bin').write_bytes(wire)
    fresh = subprocess.run([sys.executable, str(Path(codec.__file__)), str(a.proof_dir/'proof.bin'),
                            str(a.proof_dir/'statement.json')], check=True, capture_output=True, text=True)
    count = 0
    for index in [43,44,45,46,66+29+27]:
        changed = copy.deepcopy(spec)
        changed['public'][index] ^= 1
        try:
            codec.decode(wire, changed, roots)
        except (AssertionError, ValueError, KeyError, IndexError):
            count += 1
        else:
            raise AssertionError('altered public output or prepared target accepted')
    for changed in [wire[:-1], wire+b'\0']:
        try:
            codec.decode(changed, spec, roots)
        except (AssertionError, ValueError, KeyError, IndexError):
            count += 1
        else:
            raise AssertionError('altered binary framing accepted')
    report = dict(status='PASS', proof_bytes=len(wire), proof_sha256=hashlib.sha256(wire).hexdigest(),
                  public_field_count=len(spec['public']), fresh_binary_verifier=fresh.stdout.strip(),
                  rejection_checks=count, source_roots_included=True,
                  scope='Q8/Ext4 diagnostic control AIR proof; public statement separate; new AIR-to-Wasm refinement and quantum security remain unproved')
    (a.proof_dir/'control-proof-review.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
