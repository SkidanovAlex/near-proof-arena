"""Finite exact-support MCA interface checks, not a proof of exception size."""
import itertools
import json
import random
from test_independent_constraint_mixing import evaluate


def analyze(p, n, degree, minimum, even, odd):
    polys = list(itertools.product(range(p), repeat=degree))
    words = {cs: tuple(evaluate(cs,x,p) for x in range(n)) for cs in polys}
    weights = [1]*n, list(range(1,n+1)), [10]+[1]*(n-1)
    exceptions = []
    verified = 0
    for r in range(p):
        mixed = tuple(((1-r)*a+r*b)%p for a,b in zip(even,odd))
        candidates = []
        for cs, word in words.items():
            support = tuple(i for i in range(n) if word[i] == mixed[i])
            if len(support) < minimum:
                continue
            left = [a for a,aw in words.items() if all(aw[i]==even[i] for i in support)]
            right = [b for b,bw in words.items() if all(bw[i]==odd[i] for i in support)]
            candidates.append((cs,support,left,right))
        exceptional = any(not left or not right for _,_,left,right in candidates)
        if exceptional:
            exceptions.append(r)
            continue
        for cs,support,left,right in candidates:
            a,b = left[0],right[0]
            assert tuple(((1-r)*x+r*y)%p for x,y in zip(a,b)) == cs
            for weight in weights:
                original_mass = sum(weight[i] for i in support)
                joint_mass = sum(weight[i] for i in range(n)
                    if words[a][i]==even[i] and words[b][i]==odd[i])
                assert joint_mass >= original_mass
                verified += 1
    return exceptions, verified


def main():
    histogram = {}
    cases = verified = 0
    for even in itertools.product(range(3),repeat=3):
        for odd in itertools.product(range(3),repeat=3):
            exceptions, checks = analyze(3,3,1,2,even,odd)
            histogram[len(exceptions)] = histogram.get(len(exceptions),0)+1
            cases += 1
            verified += checks
    rng = random.Random(2110)
    for _ in range(64):
        even = tuple(rng.randrange(5) for _ in range(5))
        odd = tuple(rng.randrange(5) for _ in range(5))
        _,checks = analyze(5,5,2,3,even,odd)
        cases += 1
        verified += checks
    # Ordinary agreement on some support cannot preserve weighted mass.
    even,odd,r = (0,0,1),(0,0,2),2
    assert all(((1-r)*a+r*b)%3==0 for a,b in zip(even,odd))
    assert sum(a==0 and b==0 for a,b in zip(even,odd))==2
    weight = (1,1,10)
    maximum_joint_mass = max(sum(weight[i] for i in range(3)
        if even[i]==a and odd[i]==b) for a in range(3) for b in range(3))
    assert maximum_joint_mass == 10 < sum(weight)
    exceptions,_ = analyze(3,3,1,2,even,odd)
    assert r in exceptions
    print(json.dumps(dict(source_pairs=cases, weighted_lifts_checked=verified,
        f3_exception_histogram=histogram,
        ordinary_support_counterexample=dict(even=even,odd=odd,r=r,weights=weight,
            mixed_agreement_mass=12,maximum_joint_mass=maximum_joint_mass),
        scope='Finite interface validation only; no general MCA exceptional-set bound or protocol security certificate.'),indent=2))


if __name__ == '__main__':
    main()
