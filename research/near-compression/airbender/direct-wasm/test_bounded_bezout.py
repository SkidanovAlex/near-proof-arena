"""Reduce inflated certificates and compare with an independent finite linear solve."""
import json
import random
from test_bezout_smoothness import egcd, divide, sub
from test_bivariate_multiplicity import add, mul, trim


def solve(p, q, prime):
    m, n = len(p)-1, len(q)-1
    size = m+n
    matrix = [[(p[i-j] if 0 <= i-j < len(p) else 0) for j in range(n)]+
              [(q[i-j] if 0 <= i-j < len(q) else 0) for j in range(m)]+[int(i == 0)]
              for i in range(size)]
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
    rng = random.Random(88121)
    cases = constants = reductions = matrix_equations = 0
    for prime in (2, 3, 5, 17):
        accepted = 0
        while accepted < 150:
            m, n = rng.randrange(1, 7), rng.randrange(7)
            p = [rng.randrange(prime) for _ in range(m)]+[rng.randrange(1, prime)]
            q = [rng.randrange(prime) for _ in range(n)]+[rng.randrange(1, prime)]
            g, A, B = egcd(p, q, prime)
            if g != [1]: continue
            t = [rng.randrange(prime) for _ in range(rng.randrange(1, 10))]+[1]
            inflated_A = add(A, mul(t, q, prime), prime)
            inflated_B = sub(B, mul(t, p, prime), prime)
            assert trim(add(mul(inflated_A, p, prime), mul(inflated_B, q, prime), prime)) == [1]
            quotient, U = divide(inflated_A+[0, 0], q+[0], prime)
            V = trim(add(inflated_B, mul(quotient, p, prime), prime))
            assert len(U) <= n and len(V) <= m
            cert = trim(add(mul(U, p, prime), mul(V, q, prime), prime))
            assert cert == [1] and len(cert) <= m+n
            assert (U, V) == solve(p, q, prime)
            reductions += len(trim(inflated_A)) > n
            constants += n == 0
            matrix_equations += m+n
            cases += 1
            accepted += 1
    # A short prefix alone cannot certify the identity without multiplier bounds.
    p, q, A, B = [1, 1], [1], [], [1, 0, 1]
    cert = trim(add(mul(A, p, 5), mul(B, q, 5), 5))
    assert cert[:1] == [1] and cert != [1] and len(B) > 1
    print(json.dumps(dict(coprime_certificate_cases=cases, constant_second_polynomials=constants,
        inflated_certificates_reduced=reductions, independently_solved_coefficient_equations=matrix_equations,
        missing_degree_bound_counterexamples=1,
        scope='Generic Lean multiplier degree reduction and finite identity checks. Source-parameter denominator bounds and formal matrix invertibility remain open.'), indent=2))


if __name__ == '__main__': main()
