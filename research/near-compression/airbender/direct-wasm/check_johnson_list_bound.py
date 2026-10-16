"""Exhaustive small-code sanity checks and exact Johnson list arithmetic.
The Lean theorem is authoritative; this does not prove MCA or a protocol budget.
"""
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path


def run():
    prime, n, degree, threshold = 5, 5, 2, 3
    code = [tuple((a+b*x) % prime for x in range(n)) for a in range(prime) for b in range(prime)]
    assert len(set(code)) == prime**degree
    assert all(sum(x == y for x, y in zip(a, b)) <= degree-1
               for i, a in enumerate(code) for b in code[i+1:])
    maximum = cases = 0
    for word in itertools.product(range(prime), repeat=n):
        candidates = [p for p in code if sum(x == y for x, y in zip(p, word)) >= threshold]
        size = len(candidates)
        assert size*threshold**2 <= n**2+size*n*(degree-1)
        assert size*(threshold**2-n*(degree-1)) <= n**2
        maximum = max(maximum, size)
        cases += 1
    # Distinctness is essential: repeating one candidate violates the claimed
    # numerical bound, and the Lean theorem explicitly excludes such a family.
    assert 100*n*n > n*n+100*n*(degree-1)
    profiles = []
    for n, d in [(64, 16), (4096, 1024), (524288, 131072)]:
        t = 9*n//16
        gap = t*t-n*(d-1)
        assert gap > 0
        cap = n*n//gap
        q = 0
        while cap*F(t, n)**q > F(1, 2**130):
            q += 1
        assert q == 0 or cap*F(t, n)**(q-1) > F(1, 2**130)
        profiles.append(dict(domain=n, degree=d, agreement=t, gap=gap, candidate_list_cap=cap,
            candidate_pair_cap=cap*cap, constraint_root_penalty_cap=2*cap*cap,
            queries_for_isolated_list_union_tail_2powminus130=q))
    here = Path(__file__).resolve()
    report = dict(status='PASS', exhaustive_received_words=cases, codewords=len(code),
        observed_maximum_list=maximum, exhaustive_parameters=dict(prime=prime, domain=5, degree=2, agreement=3),
        profiles=profiles, source_sha256=hashlib.sha256(here.read_bytes()).hexdigest(),
        limits=['The cardinality theorem bounds any given coefficient-distinct finite family.',
            'Complete normalized list construction and support-preserving MCA remain separate obligations.',
            'Displayed tail/root penalties are components, not an end-to-end or quantum security budget.'])
    (here.parents[2]/'results/johnson-list-bound-runtime.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    run()
