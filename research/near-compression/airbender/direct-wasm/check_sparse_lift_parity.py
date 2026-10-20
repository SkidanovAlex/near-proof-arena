"""Executable Lean sparse-lift parity with actual branch_words/native folds.
Base-field challenges test zero/one factors; not a cryptographic certificate.
"""
import argparse
from array import array
import hashlib
import json
from pathlib import Path
from pq384_joint_opening import branch_words
from pq384_native_fft import NativeFFT
from pq384_one_fold import ZERO, ONE
from pq384_primitives import P
from check_whir_handoff import add, sub, mul


def flat(values):
    return array('I', [x for value in values for x in value])


class Lane:
    def __init__(self, coefficients):
        self.values = coefficients
        self.degree = len(coefficients)
    def coefficients(self, lane):
        assert lane == 0
        return self.values


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean-export', type=Path, required=True)
    p.add_argument('--fft-library', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    native = NativeFFT(args.fft_library)
    raw = args.lean_export.read_bytes()
    cases = json.loads(raw)
    rounds = 0
    cells = 0
    for n, k, point, cs, ws, lifted, repeated, cmle, wmle, factor in cases:
        embed = lambda xs: flat([(x, 0, 0, 0) for x in xs])
        actual = branch_words(Lane(cs), [ONE], 2**(n+k))
        assert actual == embed(lifted)
        assert repeated == [ws[i // 2**k] for i in range(2**(n+k))]
        c, w = actual, embed(repeated)
        smallc, smallw = embed(cs), embed(ws)
        scale = ONE
        dot = (sum(a*b for a, b in zip(cs, ws)) % P, 0, 0, 0)
        for index, r0 in enumerate(point):
            r = (r0, 0, 0, 0)
            # Same low-round schedule as pq384_weighted_joint.prove.
            q = [dot, sub(ZERO, dot), ZERO] if index < k else native.quadratic_words(smallc, smallw)
            q = [mul(scale, v) for v in q]
            assert native.quadratic_words(c, w) == q
            c, w = native.fold_words(c, r), native.fold_words(w, r)
            if index < k:
                scale = mul(scale, sub(ONE, r))
            else:
                smallc, smallw = native.fold_words(smallc, r), native.fold_words(smallw, r)
            rounds += 1
        assert tuple(c) == (cmle, 0, 0, 0)
        assert tuple(w) == (wmle, 0, 0, 0)
        assert scale == (factor, 0, 0, 0)
        assert tuple(c) == mul(scale, tuple(smallc))
        assert tuple(w) == tuple(smallw)
        cells += len(lifted)
    assert len(cases) == 75
    report = dict(status='PASS', cases=len(cases), full_vs_skipped_low_round_checks=rounds,
                  lifted_coefficient_cells=cells, lean_export_sha256=hashlib.sha256(raw).hexdigest(),
                  fft_library_sha256=hashlib.sha256(args.fft_library.read_bytes()).hexdigest(),
                  scope='Actual branch_words and native quadratic/fold functions vs executable Lean sparse coefficients, repeated weights and MLEs; base-field embedded challenges only; no commitment or QROM claim')
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
