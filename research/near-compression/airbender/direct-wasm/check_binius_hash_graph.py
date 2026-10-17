"""Connected SHA384 diagnostic; fixed graph is trusted verifier-key data.

Apply results/.../binius-hash-graph/binius.patch to the pinned checkout and build
binius-examples first. Default reruns proofs; --reuse-tmp imports the observed
prover logs/files but always performs fresh verification and negative checks.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/swirl-security-review/binius-hash-graph'
PIN = '4428e759dd27956bd5b9ae5025d67eb8ccc1accf'


def export(graph, count):
    nodes = graph['nodes'][:graph['draws'][count-1]['next_seed']+1]
    used = {v for n in nodes for k, v in n['parts'] if k == 'input'}
    inputs = {k: v for k, v in graph['inputs'].items() if k in used}
    hashes = []
    for n in nodes:
        tag = n['tag'].encode()
        frame = b'NEAR-PQ384-PRIMITIVES-V1' + struct.pack('<I', len(tag)) + tag
        frame += struct.pack('<I', len(n['parts']))
        for kind, value in n['parts']:
            if kind == 'hash':
                assert 0 <= value < len(hashes)
                data = hashes[value]
            else:
                assert kind in ('literal', 'input')
                data = bytes.fromhex(value if kind == 'literal' else inputs[value])
            frame += struct.pack('<Q', len(data)) + data
        digest = hashlib.sha384(frame).digest()
        assert digest.hex() == n['digest']
        assert (len(frame)+17+127)//128 == n['blocks']
        hashes.append(digest)
    outputs = sum(n['tag'] == 'transcript/squeeze' or i == len(nodes)-1
                  for i, n in enumerate(nodes))
    words = sum((len(bytes.fromhex(v))+7)//8 for v in inputs.values()) + outputs*6
    return dict(inputs=inputs, nodes=nodes), dict(
        challenges=count, hash_calls=len(nodes), compression_blocks=sum(n['blocks'] for n in nodes),
        public_inout_words=words, public_inout_bytes=words*8)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path('/tmp/nearproof-binius64'))
    parser.add_argument('--reuse-tmp', action='store_true')
    args = parser.parse_args()
    repo = args.repo.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == PIN
    OUT.mkdir(exist_ok=True)
    graph = json.loads(gzip.decompress((OUT.parent/'gkr-hash-graph/graph.json.gz').read_bytes()))
    env = os.environ.copy()
    env['RAYON_NUM_THREADS'] = '4'
    env.pop('NEARPROOF_GRAPH_BAD_INPUT', None)
    exe = str(repo/'target/release/binius-examples')
    def save_log(label, log):
        (OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(), mtime=0))
        return re.sub(r'\x1b\[[0-9;]*m', '', log)
    def run(label, path, command, expected=0, bad=False):
        e = env.copy()
        if bad:
            e['NEARPROOF_GRAPH_BAD_INPUT'] = '1'
        p = subprocess.run([exe, 'nearproof_hash_graph', '--graph', str(path), *command,
                            '--graph', str(path)], cwd=repo, env=e, capture_output=True, text=True)
        log = save_log(label, p.stdout+p.stderr)
        assert p.returncode == expected, (label, p.returncode, log[-1500:])
        return log
    results = []
    for count in (8, 64, 437):
        sliced, result = export(graph, count)
        path = OUT/f'graph-{count}.json'
        path.write_text(json.dumps(sliced, separators=(',', ':'))+'\n')
        proof = OUT/f'proof-{count}.bin'
        if args.reuse_tmp:
            log = save_log(f'prove-{count}', Path(f'/tmp/nearproof-binius-graph-{count}.log').read_text())
            if count != 437:
                proof.write_bytes(Path(f'/tmp/nearproof-binius-graph-{count}.proof').read_bytes())
        else:
            log = run(f'prove-{count}', path, ['prove', '--output', str(proof)],
                      expected=101 if count == 437 else 0)
        if count == 437:
            assert 'the wiring address needs 67 bits; at most 63 fit' in log
            result.update(status='SETUP_ADDRESS_LIMIT', proof_bytes=None)
        else:
            assert 'Proof written to' in log and 'Verify PCS Opening' in log
            result.update(status='PROVED_AND_FRESH_VERIFIED', serialized_proof_bytes=proof.stat().st_size,
                          proof_payload_bytes=int(re.search(r'proof_size_bytes[^0-9]+([0-9]+)', log)[1]))
            run(f'fresh-{count}', path, ['verify', str(proof)])
            if count == 64:
                log = run('bad-input-64', path, ['verify', str(proof)], expected=1, bad=True)
                assert 'invalid assertion: value is not zero' in log, log[-1500:]
                data = bytearray(proof.read_bytes())
                data[len(data)//2] ^= 1
                altered = OUT/'altered-proof-64.bin'
                altered.write_bytes(data)
                log = run('bad-proof-64', path, ['verify', str(altered)], expected=1)
                assert 'Merkle tree error' in log, log[-1500:]
        results.append(result)
    report = dict(upstream_commit=PIN, results=results,
        negative_checks=['changed public input: proof-verifier rejection', 'changed proof: Merkle rejection'],
        security='Pinned SECURITY_BITS=96 is not a complete soundness bound or PQ128 certification; SHA256 default suite.',
        scope=['Fixed graph and literal framing are trusted key data; hash parents use computed digest wires.',
               'Public squeeze digests and final seed; public inputs are outside serialized proof.',
               'CLI fresh verification computes reference public outputs using host SHA384 and evaluates a witness.',
               'No field sampling, GKR arithmetic, native prefix, PCS verifier, full NEAR, or Lean circuit refinement.',
               'Fixed observed squeeze schedule does not prove arbitrary rejection-sampling control flow.',
               'Full graph failed setup, not cryptographic verification. No full-graph size exists.'])
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
