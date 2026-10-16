"""Independent RS encoding validation using direct MLE evaluation, no FFT/Mobius.

This checks commitment encoding, not proximity, Fiat-Shamir or QROM soundness.
"""
import json
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from pq384_primitives import P, field_words, merkle_tree, verify_path, u64


def context(n, width, omega):
    return (b'NEAR-PQ384-RS-V1/row-lowbit-mobius/columns-separate/zero-pad4/'
            b'natural-domain/column-major-pairs/le-u32'
            + b''.join(u64(v) for v in (P, n, width, 4*n, omega)))


def evaluate(rows, x):
    # The diagonal x,x²,x⁴,... of the multilinear polynomial. This does not
    # construct monomial coefficients or call the prover's FFT algorithm.
    a = rows
    while len(a) > 1:
        a = [[(v + x*(w-v)) % P for v, w in zip(a[i], a[i+1])]
             for i in range(0, len(a), 2)]
        x = x*x % P
    return a[0]


def pair(rows, omega, index):
    x = pow(omega, index, P)
    return [v for ab in zip(evaluate(rows, x), evaluate(rows, (-x) % P)) for v in ab]


def run(binary, rows, full):
    n, width = len(rows), len(rows[0]); half = 2*n
    indices = list(range(half)) if full else [0, 13, half-1]
    omega = pow(440564289, (1 << 27)//(4*n), P)
    ctx = context(n, width, omega)
    with tempfile.TemporaryDirectory(prefix='near-pq384-rs-') as d:
        src, dst = Path(d)/'input.json', Path(d)/'output.json'
        src.write_text(json.dumps({'rows': rows, 'indices': indices}))
        start = time.monotonic()
        subprocess.run([binary, str(src), str(dst)], check=True, capture_output=True)
        elapsed = time.monotonic()-start
        out = json.loads(dst.read_text())
    assert out['profile'] == 'near-pq384-rs-v1'
    assert (out['rows'], out['width'], out['domain_size'], out['omega']) == (n,width,4*n,omega)
    assert bytes.fromhex(out['context_hex']) == ctx
    root = struct.pack('<12I', *out['root'])
    assert [o['index'] for o in out['openings']] == indices
    negatives = 0
    for opening in out['openings']:
        i = opening['index']; leaf = opening['leaf']
        assert leaf == pair(rows, omega, i), ('RS mismatch', n,width,i)
        payload = field_words(leaf)
        path = [struct.pack('<12I', *v) for v in opening['path']]
        assert verify_path(root, ctx, half, i, payload, path)
        altered = leaf.copy(); altered[0] = (altered[0]+1)%P
        bad_path = path.copy(); bad_path[0] = bytes([path[0][0]^1])+path[0][1:]
        cases = [(ctx,half,i,field_words(altered),path),
                 (ctx+b'x',half,i,payload,path), (ctx,half,i^1,payload,path),
                 (ctx,half*2,i,payload,path), (ctx,half,i,payload,bad_path)]
        for args in cases:
            try: verify_path(root,*args)
            except ValueError: negatives += 1
            else: raise AssertionError('accepted changed opening')
    if full:
        expected, _ = merkle_tree([field_words(pair(rows,omega,i)) for i in indices],ctx)
        assert root == expected
    return {'rows':n,'width':width,'root_hex':root.hex(),
            'checked_pairs':len(indices),'full_root_reconstruction':full,
            'negative_checks':negatives,'native_seconds_including_io':elapsed}


def main():
    binary, source, report = sys.argv[1:]
    rows = json.loads(Path(source).read_text())['rows']
    cases = [run(binary,[[r[c] for c in range(4)] for r in rows[:16]],True),
             run(binary,[[0,1],[P-1,P-2]],True),
             run(binary,rows,False)]
    result = {'status':'PASS','source':source,'cases':cases,
              'scope':'SHA-384 RS commitment encoding only; no PCS proximity or security claim',
              'independent_reference':'Direct multilinear folding at x,x^2,x^4; no Mobius or FFT',
              'large_case_limit':'Three complete vector pairs and their Merkle paths checked; full root not independently reconstructed'}
    Path(report).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__': main()
