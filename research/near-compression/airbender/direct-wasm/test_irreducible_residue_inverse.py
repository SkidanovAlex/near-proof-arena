"""Exhaustive residue inversion, normal forms, and reducible-modulus negatives."""
import itertools
import json
from test_bezout_smoothness import divide, egcd, sub
from test_bivariate_multiplicity import add, mul, trim
from test_polynomial_bezout_existence import irreducible


def main():
    moduli = inverses = representative_checks = uniqueness_checks = constants = 0
    witnesses = []
    for p, max_degree in ((2, 3), (3, 3), (5, 2)):
        for d in range(1, max_degree+1):
            for cs in itertools.product(range(p), repeat=d):
                h = list(cs)+[1]
                if not irreducible(h, p):
                    continue
                moduli += 1
                residues = [trim(list(r)) for r in itertools.product(range(p), repeat=d)]
                for a in residues:
                    # Canonical uniqueness is tested for every pair of bounded representatives.
                    for b in residues:
                        congruent = not divide(sub(a, b, p), h, p)[1]
                        assert congruent == (a == b)
                        uniqueness_checks += 1
                    for t in ([], [1], [p-1, 1, 1]):
                        rep = add(a, mul(t, h, p), p)+[0, 0]
                        assert divide(rep, h, p)[1] == a
                        representative_checks += 1
                    if not a:
                        assert egcd(a, h, p)[0] == h
                        continue
                    g, A, B = egcd(a, h, p)
                    assert g == [1]
                    inverse = divide(A, h, p)[1]
                    assert len(inverse) <= d
                    assert divide(sub(mul(inverse, a, p), [1], p), h, p)[1] == []
                    # Independent exhaustive multiplication table confirms a unique inverse.
                    solutions = [b for b in residues if divide(mul(a, b, p), h, p)[1] == [1]]
                    assert solutions == [inverse]
                    # Transport the certificate to an unreduced representative a+t*h.
                    t = [1, 1]
                    rep = add(a, mul(t, h, p), p)
                    adjusted_B = sub(B, mul(A, t, p), p)
                    assert trim(add(mul(A, rep, p), mul(adjusted_B, h, p), p)) == [1]
                    inverses += 1
                    if d > 1 and len(witnesses) < 4:
                        witnesses.append(dict(prime=p, modulus=h, residue=a, inverse=inverse))
                for c in range(1, p):
                    assert divide([c], h, p)[1] == [c]
                    constants += 1
    # Y modulo Y^2 is nonzero but cannot have an inverse: irreducibility is essential.
    for p in (2, 3, 5):
        h, a = [0, 0, 1], [0, 1]
        assert divide(a, h, p)[1]
        assert divide(mul(a, a, p), h, p)[1] == []
        assert egcd(a, h, p)[0] != [1]
        assert all(divide(mul(a, list(b), p), h, p)[1] != [1]
                   for b in itertools.product(range(p), repeat=2))
    print(json.dumps(dict(irreducible_moduli=moduli, nonzero_residue_inverses=inverses,
        reduced_representative_checks=representative_checks,
        reduced_uniqueness_pairs=uniqueness_checks, nonzero_constants=constants,
        reducible_modulus_counterexamples=3, witnesses=witnesses,
        scope='Generic Lean inverse existence and reduced representative uniqueness; quotient equivalence/ring structure and generic root extension remain to be constructed.'), indent=2))


if __name__ == '__main__':
    main()
