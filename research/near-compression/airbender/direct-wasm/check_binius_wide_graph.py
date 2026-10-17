"""Full fixed transcript graph with the diagnostic u128 sparse-address patch.

Apply binius-hash-graph/binius.patch, then binius-wide-graph/wide-address.patch,
restore the archived lockfile and build release binius-examples with native CPU.
This does not alter cryptographic parameters or establish PQ128 security.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from check_binius_hash_graph import ROOT, PIN, export

OUT = ROOT/'results/swirl-security-review/binius-wide-graph'
BASE = OUT.parent/'binius-hash-graph'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path('/tmp/nearproof-binius64'))
    ap.add_argument('--reuse-tmp', action='store_true')
    args = ap.parse_args()
    repo = args.repo.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == PIN
    OUT.mkdir(exist_ok=True)
    graph = json.loads(gzip.decompress((OUT.parent/'gkr-hash-graph/graph.json.gz').read_bytes()))
    sliced, counts = export(graph, 437)
    assert sliced == json.loads((BASE/'graph-437.json').read_text())
    exe = str(repo/'target/release/binius-examples')
    env = os.environ.copy()
    env['RAYON_NUM_THREADS'] = '4'
    env.pop('NEARPROOF_GRAPH_BAD_INPUT', None)
    def save(label, log):
        (OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(), mtime=0))
        return re.sub(r'\x1b\[[0-9;]*m', '', log)
    def run(label, command, count=437, bad=False):
        e = env.copy()
        if bad:
            e['NEARPROOF_GRAPH_BAD_INPUT'] = '1'
        path = str(BASE/f'graph-{count}.json')
        p = subprocess.run([exe, 'nearproof_hash_graph', '--graph', path, *command,
                            '--graph', path], cwd=repo, env=e, capture_output=True, text=True)
        log = save(label, p.stdout+p.stderr)
        return p.returncode, log
    proof = OUT/'proof.bin'
    if args.reuse_tmp:
        proof.write_bytes(Path('/tmp/nearproof-binius-wide-437.proof').read_bytes())
        log = save('prove', Path('/tmp/nearproof-binius-wide-437.log').read_text())
    else:
        code, log = run('prove', ['prove', '--output', str(proof)])
        assert code == 0, log[-1500:]
    assert 'Proof written to' in log and 'Verify PCS Opening' in log
    payload = int(re.search(r'proof_size_bytes[^0-9]+([0-9]+)', log)[1])
    for label, command, count, bad in [
        ('fresh', ['verify', str(proof)], 437, False),
        ('legacy', ['verify', str(BASE/'proof-64.bin')], 64, False),
        ('bad-input', ['verify', str(proof)], 437, True),
    ]:
        code, log = run(label, command, count, bad)
        assert code == (1 if bad else 0), (label, code, log[-1500:])
        assert ('invalid assertion: value is not zero' if bad else 'Proof verified successfully') in log
    altered = bytearray(proof.read_bytes())
    altered[len(altered)//2] ^= 1
    path = OUT/'altered-proof.bin'
    path.write_bytes(altered)
    code, log = run('bad-proof', ['verify', str(path)])
    assert code == 1 and 'Merkle tree error' in log, (code, log[-1500:])
    counts.update(upstream_commit=PIN, status='FULL_FIXED_HASH_GRAPH_PROVED_AND_VERIFIED',
        proof_payload_bytes=payload, serialized_proof_bytes=proof.stat().st_size,
        proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest(),
        checks=['fresh verification', 'old 64-draw proof verifies after address widening',
                'changed public input rejected by verifier', 'changed proof rejected by Merkle authentication'],
        scope='Only fixed hash graph: no sampler, GKR arithmetic, prefix/PCS verifier, full NEAR or Lean refinement.',
        security='Unchanged diagnostic SECURITY_BITS=96 and SHA256 suite; no complete/PQ128 soundness claim.',
        public_io='Public input/output bytes are external to the proof file; graph is fixed verifier-key data.')
    (OUT/'report.json').write_text(json.dumps(counts, indent=2)+'\n')
    print(json.dumps(counts, indent=2))


if __name__ == '__main__':
    main()
