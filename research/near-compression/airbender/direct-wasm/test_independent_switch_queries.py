"""Exhaust the joint source-query / independent-mixer experiment over F3."""
import itertools
import json
from test_independent_constraint_mixing import evaluate, injected, wrong


def main():
    p = 3
    seeds = list(range(p))
    weights = [1, 2]
    families = [[(0,0)], [(1,1)], [(0,0),(1,0)], [(0,1),(2,1)], []]
    cases = experiments = 0
    for received in itertools.product(seeds, repeat=p):
        for family in families:
            for claim in seeds:
                agreements = [sum(evaluate(cs,x,p) == received[x] for x in seeds)
                    for cs in family if sum(c*w for c,w in zip(cs,weights)) % p == claim]
                threshold = 1+max(agreements, default=0)
                for q in range(3):
                    accepted = correct_queries = 0
                    for queries in itertools.product(seeds, repeat=q):
                        templates = [(2,received[2])]+[(x,received[x]) for x in queries]
                        correct = any(not wrong(cs,weights,claim,templates,p) for cs in family)
                        correct_queries += correct
                        mixed_bad = 0
                        for mixers in itertools.product(seeds, repeat=q+1):
                            good = any(injected(cs,weights,claim,templates,mixers,p)==0 for cs in family)
                            accepted += good
                            mixed_bad += any(wrong(cs,weights,claim,templates,p) and
                                injected(cs,weights,claim,templates,mixers,p)==0 for cs in family)
                            experiments += 1
                        assert mixed_bad <= len(family)*p**q
                    assert correct_queries <= len(family)*(threshold-1)**q
                    bound = len(family)*(threshold-1)**q*p**(q+1)+p**q*len(family)*p**q
                    assert accepted <= bound
                    cases += 1
    # Removing noClose is unsound: the zero polynomial/source and true old
    # claim pass all samples, whereas falsely declaring T=1 gives only 1/F.
    q, claimed_threshold = 1, 1
    accepted = p**q*p**(q+1)
    invalid_bound = (claimed_threshold-1)**q*p**(q+1)+p**q*p**q
    assert accepted > invalid_bound
    print(json.dumps(dict(cases=cases, joint_experiments=experiments,
        omitted_no_close_counterexample=dict(accepted=accepted, invalid_bound=invalid_bound),
        scope='Fixed prequery family and fixed source, ideal independent draws. No source-transfer, commitment extraction, multi-stage or QROM certificate.'), indent=2))


if __name__ == '__main__':
    main()
