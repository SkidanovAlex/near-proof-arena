"""Bounded coefficient-map bijectivity, arbitrary targets, and noncoprime negatives."""
import itertools
import json
import random
from test_bezout_smoothness import divide, egcd
from test_bivariate_multiplicity import add, mul, trim


def solve(p, q, target, prime):
    m, n = len(p)-1, len(q)-1
    size = m+n
    matrix = [[(p[i-j] if 0 <= i-j < len(p) else 0) for j in range(n)]+
              [(q[i-j] if 0 <= i-j < len(q) else 0) for j in range(m)]+
              [target[i] if i < len(target) else 0] for i in range(size)]
    for j in range(size):
        pivot = next(i for i in range(j, size) if matrix[i][j])
        matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
        inv = pow(matrix[j][j], -1, prime)
        matrix[j] = [v*inv % prime for v in matrix[j]]
        for i in range(size):
            if i != j:
                c = matrix[i][j]
                matrix[i] = [(v-c*w) % prime for v, w in zip(matrix[i], matrix[j])]
    values = [row[-1] for row in matrix]
    return trim(values[:n]), trim(values[n:])


def main():
    rng = random.Random(87112)
    cases = constant_pairs = zero_targets = exhaustive_maps = exhaustive_vectors = 0
    for prime in (2, 3, 5, 17):
        accepted = 0
        while accepted < 100:
            m, n = rng.randrange(6), rng.randrange(6)
            p = [rng.randrange(prime) for _ in range(m)]+[rng.randrange(1, prime)]
            q = [rng.randrange(prime) for _ in range(n)]+[rng.randrange(1, prime)]
            g, A, B = egcd(p, q, prime)
            if g != [1]: continue
            target = [rng.randrange(prime) for _ in range(m+n)]
            t, U = divide(mul(A, target, prime), q, prime)
            V = trim(add(mul(B, target, prime), mul(t, p, prime), prime))
            assert len(U) <= n and len(V) <= m
            assert trim(add(mul(U, p, prime), mul(V, q, prime), prime)) == trim(target)
            assert (U, V) == solve(p, q, target, prime)
            zero_targets += not any(target)
            constant_pairs += m == 0 or n == 0
            # Exhaustive coefficient-map image confirms injectivity, surjectivity
            # and a unique zero preimage without relying on Gaussian elimination.
            if prime <= 3 and m+n <= 4:
                images = set()
                zero_preimages = 0
                for vector in itertools.product(range(prime), repeat=m+n):
                    u, v = list(vector[:n]), list(vector[n:])
                    image = trim(add(mul(u, p, prime), mul(v, q, prime), prime))
                    assert len(image) <= m+n
                    key = tuple(image)
                    assert key not in images
                    images.add(key)
                    zero_preimages += not image
                    exhaustive_vectors += 1
                assert len(images) == prime**(m+n) and zero_preimages == 1
                exhaustive_maps += 1
            accepted += 1
            cases += 1
    # Coprimality cannot be dropped: p=q gives a nonzero bounded kernel vector.
    for prime in (2, 3, 5):
        p = q = [1, 1]
        u, v = [1], [prime-1]
        assert trim(add(mul(u, p, prime), mul(v, q, prime), prime)) == []
        assert egcd(p, q, prime)[0] != [1]
    print(json.dumps(dict(arbitrary_target_systems=cases, cases_with_constant_polynomial=constant_pairs,
        zero_targets=zero_targets, exhaustively_bijective_maps=exhaustive_maps,
        exhaustive_coefficient_vectors=exhaustive_vectors, noncoprime_kernel_counterexamples=3,
        scope='Formal bounded Bezout coefficient-map injectivity and surjectivity. Determinant construction and parameter-degree denominator bounds remain open.'), indent=2))


if __name__ == '__main__': main()
