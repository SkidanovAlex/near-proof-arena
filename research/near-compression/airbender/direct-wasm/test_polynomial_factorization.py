"""Exhaustive small-field regressions for degree descent and factor trees."""
import itertools
import json
from test_bezout_smoothness import divide, derivative, egcd
from test_bivariate_multiplicity import add, mul, trim


def candidates(prime, degree):
    for d in range(1, degree//2+1):
        for cs in itertools.product(range(prime), repeat=d):
            yield list(cs)+[1]


def factor_tree(poly, prime):
    poly = trim(poly)
    assert poly, 'zero polynomial has no valid nonzero factor tree'
    degree = len(poly)-1
    if degree == 0:
        return ('scalar', poly[0])
    for a in candidates(prime, degree):
        b, remainder = divide(poly, a, prime)
        if not remainder:
            assert 0 < len(a)-1 < degree and 0 < len(b)-1 < degree
            assert a[-1]*b[-1] % prime == poly[-1]
            return ('product', factor_tree(a, prime), factor_tree(b, prime))
    return ('factor', poly)


def inspect(tree, prime):
    if tree[0] == 'scalar':
        assert tree[1] != 0
        return [tree[1]], [], 0
    if tree[0] == 'factor':
        q = tree[1]
        assert len(q)>1
        assert all(divide(q, a, prime)[1] for a in candidates(prime, len(q)-1))
        # An independent root test is also complete in degrees two and three.
        if len(q) in (3, 4):
            assert all(sum(c*pow(x, i, prime) for i, c in enumerate(q)) % prime
                       for x in range(prime))
        return q, [q], 0
    a, af, ad = inspect(tree[1], prime)
    b, bf, bd = inspect(tree[2], prime)
    result = trim(mul(a, b, prime))
    assert len(result)-1 == (len(a)-1)+(len(b)-1)
    return result, af+bf, 1+max(ad, bd)


def main():
    cases = leaves = extracted = repeated = 0
    maximum_depth = 0
    smooth_factor_certificates = 0
    witnesses = []
    for prime in (2, 3, 5):
        for degree in range(5):
            for cs in itertools.product(range(prime), repeat=degree):
                for leading in range(1, prime):
                    poly = list(cs)+[leading]
                    tree = factor_tree(poly+[0, 0], prime)
                    reconstructed, factors, depth = inspect(tree, prime)
                    assert reconstructed == poly
                    if degree:
                        assert factors
                        for q in factors:
                            quotient, remainder = divide(poly, q, prime)
                            assert not remainder and trim(mul(quotient, q, prime)) == poly
                            assert len(q) <= len(poly)
                            if degree < prime:
                                dq = derivative(q, prime)
                                g, A, B = egcd(q, dq, prime)
                                assert g == [1]
                                assert trim(add(mul(A, q, prime), mul(B, dq, prime), prime)) == [1]
                                smooth_factor_certificates += 1
                        extracted += 1
                    else:
                        assert not factors
                    repeated += len({tuple(q) for q in factors}) < len(factors)
                    leaves += len(factors)
                    maximum_depth = max(maximum_depth, depth)
                    cases += 1
                    if depth >= 2 and len(witnesses) < 3:
                        witnesses.append(dict(prime=prime, polynomial=poly, tree=tree))
    try:
        factor_tree([0, 0], 3)
    except AssertionError:
        pass
    else:
        raise AssertionError('zero input accepted')
    print(json.dumps(dict(nonzero_polynomials=cases, irreducible_leaves=leaves,
        small_degree_factor_certificates=smooth_factor_certificates,
        nonconstant_inputs_with_extracted_divisor=extracted,
        repeated_factor_inputs=repeated, maximum_tree_depth=maximum_depth,
        zero_input_rejections=1, witnesses=witnesses,
        scope='Exhaustive nonzero polynomials of degree at most four over F2/F3/F5. Formal Lean existence is generic; efficient factorization and algebraic extension construction remain separate.'), indent=2))


if __name__ == '__main__':
    main()
