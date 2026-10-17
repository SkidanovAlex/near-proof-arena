"""Executable Lean sparse polynomial vs actual branch_words accumulator."""
import argparse
import hashlib
import json
from pathlib import Path
from pq384_joint_opening import branch_words
from pq384_primitives import P
from check_whir_handoff import add, mul


class Lanes:
    def __init__(self, degree, lanes):
        self.degree, self.values = degree, lanes
    def coefficients(self, lane):
        return self.values[lane]


def horner(coefficients, x):
    out = 0
    for c in reversed(coefficients):
        out = (out*x+c) % P
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean-export', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    raw = a.lean_export.read_bytes()
    cases = json.loads(raw)
    cells = extension_checks = 0
    for n, k, lanes, beta, x, coefficients, value in cases:
        D = 2**(n+k)
        cache = Lanes(2**n, lanes)
        words = branch_words(cache, [(b,0,0,0) for b in beta], D)
        assert list(words) == [z for c in coefficients for z in (c,0,0,0)]
        assert horner(coefficients, x) == value
        assert sum(b*horner(cs, pow(x,2**k,P)) for b,cs in zip(beta,lanes)) % P == value
        mixed = [(3,5,7,11),(0,0,0,0),(13,17,19,23)]
        wide = branch_words(cache, mixed, D)
        actual = (0,0,0,0)
        for i in reversed(range(D)):
            actual = add(mul(actual,(x,0,0,0)),tuple(wide[4*i:4*i+4]))
        expected = (0,0,0,0)
        for b,cs in zip(mixed,lanes):
            expected = add(expected,mul(b,(horner(cs,pow(x,2**k,P)),0,0,0)))
        assert actual == expected
        cells += D
        extension_checks += 1
    assert len(cases) == 48
    report = dict(status='PASS', cases=len(cases), coefficient_cells=cells,
                  mixed_extension_evaluations=extension_checks,
                  lean_export_sha256=hashlib.sha256(raw).hexdigest(),
                  scope='Executable Lean coefficient/evaluation parity with actual branch_words for empty, short and full lanes, lift0..3, source dimension0..3, x=0/1/17. Extra mixed Ext4 beta regression. Not native FFT correctness, commitment binding, or quantum soundness.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
