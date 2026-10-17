"""Executable Lean DIT stage model vs mutable stages and actual native FFT."""
import argparse
import hashlib
import json
from pathlib import Path
from pq384_native_fft import NativeFFT
from pq384_primitives import P


def horner(cs, x):
    value = 0
    for c in reversed(cs):
        value = (value*x+c) % P
    return value


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean-export', type=Path, required=True)
    p.add_argument('--library', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    raw = a.lean_export.read_bytes()
    cases = json.loads(raw)
    native = NativeFFT(a.library)
    stages_checked = cells = pairs = mixed = 0
    for n, omega, cs, stages in cases:
        N = 2**n
        assert omega == pow(440564289,(1<<27)//N,P)
        assert n == 0 or pow(omega,N//2,P) == P-1
        padded = cs+[0]*(N-len(cs))
        values = padded[:]
        j = 0
        for i in range(1,N):
            bit = N >> 1
            while j & bit:
                j ^= bit
                bit >>= 1
            j ^= bit
            if i < j:
                values[i],values[j] = values[j],values[i]
        assert values == stages[0]
        stages_checked += 1
        width = 2
        for expected in stages[1:]:
            step = pow(omega,N//width,P)
            for base in range(0,N,width):
                w = 1
                for offset in range(width//2):
                    lo = base+offset
                    hi = lo+width//2
                    u,v = values[lo],values[hi]*w % P
                    values[lo],values[hi] = (u+v)%P,(u-v)%P
                    w = w*step % P
            assert values == expected
            stages_checked += 1
            width *= 2
        actual = native.fft([(c,0,0,0) for c in padded])
        assert actual == [(v,0,0,0) for v in stages[-1]]
        for i in range(N):
            assert actual[i][0] == horner(cs,pow(omega,i,P))
            cells += 1
        for i in range(N//2):
            assert actual[i+N//2][0] == horner(cs,-pow(omega,i,P))
            pairs += 1
        wide = [(v,(3*i+5)%P,(i*i+7)%P,(P-1-i)%P) for i,v in enumerate(padded)]
        result = native.fft(wide)
        for i in range(N):
            assert result[i] == tuple(horner([c[k] for c in wide],pow(omega,i,P)) for k in range(4))
            mixed += 1
    assert len(cases) == 24
    report = dict(status='PASS', cases=len(cases), stage_arrays=stages_checked,
                  native_values=cells, plus_minus_pairs=pairs, mixed_ext4_values=mixed,
                  lean_export_sha256=hashlib.sha256(raw).hexdigest(),
                  library_sha256=hashlib.sha256(a.library.read_bytes()).hexdigest(),
                  scope='Dimensions0..7, empty/short/full inputs. Exact Lean functional-stage parity, mutable-loop regression and native polynomial/pair checks. Native permutation, mutable writes and machine arithmetic remain formally unproved.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
