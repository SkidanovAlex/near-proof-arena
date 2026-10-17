#!/usr/bin/env python3
"""Exercise the actual Lean block checker; interpreter timings, not proof costs."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent

def main():
    runs = []
    for repetition in range(3):
        proc = subprocess.run(['lake', 'env', 'lean', '--run', 'BlockBatchSmoke.lean'],
                              cwd=ROOT, capture_output=True, text=True, timeout=120, check=True)
        lines = proc.stdout.strip().splitlines()
        digest = bytes(ast.literal_eval(lines[0].removeprefix('sha512_abc=')))
        assert digest == hashlib.sha512(b'abc').digest(), 'SHA-512 known-answer mismatch'
        cases = []
        for line in lines[1:]:
            row = dict(token.split('=', 1) for token in line.split())
            cases.append({k: v if k == 'case' else int(v) for k, v in row.items()})
        assert [(r['case'], r['batches'], r['mutations_rejected']) for r in cases] == [
            ('empty', 0, 0), ('same_block', 1, 5), ('cross_block', 2, 6), ('dense', 1, 5)]
        runs.append({'repetition': repetition, 'cases': cases})
    sources = [ROOT / 'BlockBatchSmoke.lean', Path(__file__).resolve()]
    sources += sorted((ROOT / 'NearCompression').glob('*.lean'))
    sources.append(ROOT.parent.parent / 'spec/lean/v3/NearSpecV3/SHA512.lean')
    result = {
        'time_unix': time.time(), 'mode': 'lake env lean --run (interpreter)',
        'checks': ['cached payload wrapper witness and result parity', 'direct memory replacement', 'full root rebuild', 'mutation rejection'],
        'memory_bytes': 65536, 'block_bytes': 4096, 'depth': 4,
        'hash': 'NearSpecV3.sha512, abc checked independently with hashlib',
        'limitations': ['Not a succinct proof or quantum security result',
                       'Reference generator rebuilds trees', 'One CPU, shared host, three repetitions',
                       'Timing excludes process startup, final independent checks and mutation checks',
                       'Memory oracle uses direct byte replacements; root oracle rebuilds with the same formal tree code'],
        'source_sha256': {str(p.relative_to(ROOT.parent.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        'runs': runs}
    target = ROOT / 'results/block-checker-lean-smoke.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS: 12 accepted cases, 48 rejected mutations; {target}')

if __name__ == '__main__':
    main()
