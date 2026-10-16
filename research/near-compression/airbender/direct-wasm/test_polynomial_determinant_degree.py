"""Division-free polynomial determinant versus independent numeric elimination."""
import itertools
import json
import random
from test_bivariate_multiplicity import add, mul, trim
from test_independent_constraint_mixing import evaluate


def determinant(matrix, prime):
    if not matrix: return [1]
    result = []
    for j, entry in enumerate(matrix[0]):
        minor = [[v for k, v in enumerate(row) if k != j] for row in matrix[1:]]
        term = mul(entry, determinant(minor, prime), prime)
        if j % 2: term = [-c % prime for c in term]
        result = add(result, term, prime)
    return trim(result)


def numeric_det(matrix, prime):
    a = [row[:] for row in matrix]
    result = 1
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None: return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result % prime
        value = a[j][j]
        result = result*value % prime
        inv = pow(value, -1, prime)
        for i in range(j+1, len(a)):
            factor = a[i][j]*inv % prime
            a[i] = [(v-factor*w) % prime for v, w in zip(a[i], a[j])]
    return result


def permutation_det(matrix, prime):
    result = []
    for perm in itertools.permutations(range(len(matrix))):
        term = [1]
        for i, j in enumerate(perm): term = mul(term, matrix[i][j], prime)
        parity = sum(perm[i] > perm[j] for i in range(len(perm)) for j in range(i+1, len(perm))) % 2
        if parity: term = [-c % prime for c in term]
        result = add(result, term, prime)
    return trim(result)


def main():
    rng = random.Random(45121)
    matrices = specializations = nonzero_cases = derivative_cases = derivative_nonzero = 0
    for prime in (2, 3, 5, 17):
        for _ in range(60):
            n, D = rng.randrange(5), rng.randrange(4)
            matrix = [[[rng.randrange(prime) for _ in range(D+1)]+[0] for _ in range(n)] for _ in range(n)]
            det = determinant(matrix, prime)
            assert det == permutation_det(matrix, prime)
            assert len(det) <= n*D+1
            roots = 0
            for z in range(prime):
                actual = numeric_det([[evaluate(entry, z, prime) for entry in row] for row in matrix], prime)
                assert actual == evaluate(det, z, prime)
                roots += actual == 0
                specializations += 1
            if det:
                assert roots <= n*D
                nonzero_cases += 1
            matrices += 1
        for _ in range(25):
            d, D = rng.randrange(1, 4), rng.randrange(1, 4)
            p = [[rng.randrange(prime) for _ in range(D+1)] for _ in range(d+1)]
            if not any(p[-1]): p[-1][0] = 1
            q = [[(i+1)*c % prime for c in p[i+1]] for i in range(d)]
            n = d-1
            matrix = []
            for i in range(d+n):
                row = [p[i-j] if 0 <= i-j < len(p) else [] for j in range(n)]
                row += [q[i-j] if 0 <= i-j < len(q) else [] for j in range(d)]
                matrix.append(row)
            det = determinant(matrix, prime)
            assert len(det) <= (2*d-1)*D+1
            roots = 0
            for z in range(prime):
                assert evaluate(det, z, prime) == numeric_det([[evaluate(v, z, prime) for v in row] for row in matrix], prime)
                roots += evaluate(det, z, prime) == 0
            if det:
                assert roots <= (2*d-1)*D
                derivative_nonzero += 1
            derivative_cases += 1
    # Nonzeroness is essential: zero determinant vanishes everywhere despite D=0.
    singular = [[[1], [1]], [[1], [1]]]
    assert determinant(singular, 5) == []
    assert all(numeric_det([[1, 1], [1, 1]], 5) == 0 for _ in range(5))
    print(json.dumps(dict(polynomial_matrices=matrices, numeric_specializations=specializations,
        nonzero_determinant_root_bounds=nonzero_cases, derivative_bezout_matrices=derivative_cases,
        nonzero_derivative_determinants=derivative_nonzero, missing_nonzero_counterexamples=1,
        scope='Lean determinant source-degree and evaluation bounds. Nonzeroness from Bezout-map invertibility and inverse/denominator interpretation remain open.'), indent=2))


if __name__ == '__main__': main()
