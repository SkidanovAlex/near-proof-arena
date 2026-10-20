"""Quotient arithmetic is independent of polynomial representatives."""
import itertools
import json
from test_bezout_smoothness import divide, sub
from test_bivariate_multiplicity import add, mul, trim
from test_polynomial_bezout_existence import irreducible


def main():
    moduli = pairs = triples = inverse_elements = 0
    reducible_nonunits = 0
    for p in (2, 3, 5):
        for d in (1, 2):
            for cs in itertools.product(range(p), repeat=d):
                h = list(cs)+[1]
                moduli += 1
                def normal(a):
                    return divide(a, h, p)[1]
                def plus(a, b):
                    return normal(add(a, b, p))
                def times(a, b):
                    return normal(mul(a, b, p))
                def neg(a):
                    return normal(sub([], a, p))
                residues = [trim(list(a)) for a in itertools.product(range(p), repeat=d)]
                is_irreducible = irreducible(h, p)
                for a in residues:
                    ap = add(a, mul([1, 1], h, p), p)+[0, 0]
                    app = add(ap, mul([p-1, 0, 1], h, p), p)
                    assert normal(a) == normal(ap) == normal(app)
                    assert normal(sub(ap, a, p)) == normal(sub(a, ap, p)) == []
                    assert neg(a) == neg(ap)
                    if a:
                        inverses = [b for b in residues if times(a, b) == [1]]
                        if is_irreducible:
                            assert len(inverses) == 1
                            inverse_elements += 1
                        elif not inverses:
                            reducible_nonunits += 1
                    for b in residues:
                        bp = add(b, mul([0, 1], h, p), p)+[0]
                        assert plus(a, b) == plus(ap, bp)
                        assert times(a, b) == times(ap, bp)
                        assert times(a, b) == times(b, a)
                        assert (normal(sub(a, b, p)) == []) == (a == b)
                        pairs += 1
                        for c in residues:
                            assert times(times(a, b), c) == times(a, times(b, c))
                            assert times(plus(a, b), c) == plus(times(a, c), times(b, c))
                            triples += 1
    assert reducible_nonunits > 0
    print(json.dumps(dict(nonzero_monic_moduli=moduli,
        representative_independence_pairs=pairs, quotient_law_triples=triples,
        irreducible_nonzero_quotient_inverses=inverse_elements,
        reducible_nonunit_elements=reducible_nonunits,
        scope='Actual Lean quotient and well-defined operations, selected ring laws and quotient inverse existence. Full field instance and root construction remain open.'), indent=2))


if __name__ == '__main__':
    main()
