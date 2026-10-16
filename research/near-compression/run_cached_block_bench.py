#!/usr/bin/env python3
"""Compare reference and cached Lean witness generation, including initialization."""
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent

def main():
    runs = []
    for repetition in range(3):
        proc = subprocess.run(['lake', 'env', 'lean', '--run', 'CachedBlockBench.lean'],
                              cwd=ROOT, capture_output=True, text=True, timeout=120, check=True)
        cases = []
        for line in proc.stdout.strip().splitlines():
            row = dict(token.split('=', 1) for token in line.split())
            cases.append({k: v if k == 'case' else int(v) for k, v in row.items()})
        assert [(r['case'], r['batches']) for r in cases] == [
            ('one_batch', 1), ('sixteen_blocks', 16), ('revisits', 16), ('larger_sparse', 8)]
        runs.append({'repetition': repetition, 'cases': cases})
        print(f'Completed repetition {repetition + 1}/3', flush=True)
    sources = [ROOT / 'CachedBlockBench.lean', Path(__file__).resolve()]
    sources += sorted((ROOT / 'NearCompression').glob('*.lean'))
    sources.append(ROOT.parent.parent / 'spec/lean/v3/NearSpecV3/SHA512.lean')
    result = {
        'time_unix': time.time(), 'mode': 'lake env lean --run (interpreter)',
        'block_bytes': 4096, 'hash': 'NearSpecV3.sha512',
        'checks': ['exact witness field equality', 'initial root equality',
                   'accepted result equals full actual-state root rebuild', 'direct memory replacement oracle'],
        'limitations': ['Not succinct proof or quantum security evidence',
                       'Single CPU on shared host; reference always measured before cached',
                       'Three repetitions; cache construction included separately',
                       'Input plans preconstructed; grouping and final checks excluded from timings',
                       'Root oracle shares reference tree code'],
        'source_sha256': {str(p.relative_to(ROOT.parent.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        'runs': runs}
    target = ROOT / 'results/cached-block-lean-bench.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS: 12 cases with exact witness and state parity; {target}')

if __name__ == '__main__':
    main()
