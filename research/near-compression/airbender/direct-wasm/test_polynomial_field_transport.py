"""Exercise certificate transport at genuinely new quadratic-extension roots."""
import itertools
import json
from test_bezout_smoothness import derivative, egcd
from test_bivariate_multiplicity import add, mul


def main():
    roots = certificates = hom_checks = 0
    witnesses = []
    for p, nonsquare in ((3, 2), (5, 2), (7, 3)):
        assert all(x*x % p != nonsquare for x in range(p))
        zero, one = (0, 0), (1, 0)
        elements = list(itertools.product(range(p), repeat=2))
        def plus(a, b):
            return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
        def times(a, b):
            return ((a[0]*b[0]+nonsquare*a[1]*b[1]) % p,
                    (a[0]*b[1]+a[1]*b[0]) % p)
        def embed(x):
            return (x % p, 0)
        def ev(cs, x):
            result = zero
            for c in reversed(cs):
                result = plus(c, times(x, result))
            return result
        # Independently check this concrete extension's inverses and operations.
        for a in elements:
            if a != zero:
                assert any(times(a, b) == one for b in elements)
            for b in elements:
                assert times(a, b) == times(b, a)
                for c in elements:
                    assert times(times(a, b), c) == times(a, times(b, c))
                    assert times(a, plus(b, c)) == plus(times(a, b), times(a, c))
        for a, b in itertools.product(range(p), repeat=2):
            assert embed((a+b) % p) == plus(embed(a), embed(b))
            assert embed(a*b % p) == times(embed(a), embed(b))
            hom_checks += 1
        q = [(-nonsquare) % p, 0, 1]
        dq = derivative(q, p)
        g, A, B = egcd(q, dq, p)
        assert g == [1]
        identity = add(mul(A, q, p), mul(B, dq, p), p)
        assert identity[0] == 1 and not any(identity[1:])
        assert all(ev(list(map(embed, q)), embed(x)) != zero for x in range(p))
        mapped_q, mapped_dq = list(map(embed, q)), list(map(embed, dq))
        actual_derivative = [times(embed(i), mapped_q[i]) for i in range(1, len(q))]
        assert actual_derivative == mapped_dq
        new_roots = []
        for x in elements:
            cert = plus(times(ev(list(map(embed, A)), x), ev(mapped_q, x)),
                        times(ev(list(map(embed, B)), x), ev(mapped_dq, x)))
            assert cert == one
            certificates += 1
            if ev(mapped_q, x) == zero:
                assert x[1] != 0 and ev(actual_derivative, x) != zero
                new_roots.append(x)
                roots += 1
        assert len(new_roots) == 2
        # A corrupt zero certificate cannot establish smoothness.
        assert plus(times(zero, ev(mapped_q, new_roots[0])),
                    times(zero, ev(mapped_dq, new_roots[0]))) != one
        witnesses.append(dict(prime=p, nonsquare=nonsquare, polynomial=q,
                              A=A, B=B, extension_roots=new_roots))
    print(json.dumps(dict(coefficient_homomorphism_pairs=hom_checks,
        extension_certificate_evaluations=certificates, new_smooth_roots=roots,
        witnesses=witnesses,
        scope='Concrete quadratic-extension regressions; generic Lean transport is proved. Generic extension construction and full MCA remain open.'), indent=2))


if __name__ == '__main__':
    main()
