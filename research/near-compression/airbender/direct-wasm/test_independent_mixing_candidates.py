"""Exhaustive fixed-oracle Johnson/mixer checks; no extraction claim."""
import itertools
import json
import math
from test_independent_constraint_mixing import evaluate, injected, wrong


def main():
    cases = 0
    experiments = 0
    for p, degree, threshold in [(3, 2, 2), (3, 2, 3), (5, 2, 3)]:
        domain = range(p)
        polys = list(itertools.product(domain, repeat=degree))
        # Exhaust all received words over F3; structured non-codewords over F5.
        words = list(itertools.product(domain, repeat=p)) if p == 3 else [
            tuple((x*x + a*x + b) % p for x in domain) for a in domain for b in domain]
        gap = threshold**2 - p*(degree-1)
        assert gap > 0
        for received in words:
            family = [cs for cs in polys if sum(evaluate(cs, x, p) == received[x]
                      for x in domain) >= threshold]
            assert len(family)*gap <= p*p
            weights, claim = [1, 2], 1
            templates = [(0, received[0]), (1, received[1])]
            bad = 0
            for mixers in itertools.product(domain, repeat=len(templates)):
                bad += any(wrong(cs, weights, claim, templates, p) and
                           injected(cs, weights, claim, templates, mixers, p) == 0
                           for cs in family)
                experiments += 1
            assert bad <= len(family)*p**(len(templates)-1)
            assert bad*p*gap <= p*p*p**len(templates)
            cases += 1
    # An incomplete coefficient alphabet cannot provide a complete list.
    missing = (1, 0)
    assert missing not in list(itertools.product([0], repeat=2))
    assert all(evaluate(missing, x, 3) == 1 for x in range(3))
    # Zero Johnson gap has no list-size consequence.
    assert 2**2 - 4*(2-1) == 0
    stages = []
    for degree, rate in [(131072,8),(16384,16),(2048,32),(256,64),
                         (32,128),(4,256),(2,256)]:
        n = degree*rate
        target = n*(degree-1) + (n*degree + 9)//10
        threshold = math.isqrt(target)
        threshold += threshold*threshold < target
        gap = threshold*threshold - n*(degree-1)
        assert gap > 0 and threshold <= n
        cap = n*n//gap
        assert cap <= 10*rate
        stages.append(dict(degree=degree, rate=rate, domain_size=n,
                           required_agreement=threshold, johnson_gap=gap,
                           proven_fixed_oracle_list_cap=cap))
    print(json.dumps(dict(cases=cases, mixer_experiments=experiments, stages=stages,
        scope='Ideal fixed-oracle agreement-conditioned mixing only. Protocol agreement, extraction, adaptive composition and QROM remain unproved.'), indent=2))


if __name__ == '__main__':
    main()
