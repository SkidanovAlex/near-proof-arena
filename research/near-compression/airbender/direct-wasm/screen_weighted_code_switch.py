"""Conditional code-switch geometry for the retained weighted slice.
No new soundness claim: repeated weighted code switching is not implemented.
"""
import itertools
import json
import math
import random
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from estimate_ext8_multiproof_geometry import frontier
from screen_whir_query_regimes import minimum_queries

RATES = (4, 16, 64)  # square rates keep Johnson factors exact rational
BUDGETS = (134, 198, 220)

@lru_cache(None)
def geometry(n, q):
    # Expected occupied leaves and minimal sibling frontier, uniform replacement.
    absent = lambda size: 0.0 if size == n else math.exp(q * math.log1p(-size/n))
    leaves = -n * math.expm1(q * math.log1p(-1/n)) if n > 1 else 1.0
    hashes = sum((n//s)*(absent(s)-absent(2*s)) for s in (1 << i for i in range(n.bit_length()-1)))
    return leaves, hashes

@lru_cache(None)
def queries(regime, rate, bits):
    rho=F(1,rate)
    factor={'current':(2+rho)/3, 'unique':(1+rho)/2,
            'johnson':F(21,20*math.isqrt(rate))}[regime]
    return minimum_queries(factor, bits)


def stage(degree, rate, skipped, regime, widths, bits, extension=8, hash_bytes=48):
    n=degree*rate//(1<<skipped)
    q=queries(regime,rate,bits)
    leaves,hashes=geometry(n,q)
    copies=1<<(skipped-1)
    # Each source coset contains 2^skipped values, hence 2^(skipped-1) paired leaves.
    header=12*extension*skipped+hash_bytes+4*extension
    cost=header+copies*(sum(widths)*leaves+hash_bytes*len(widths)*hashes)
    return dict(degree=degree,rate=rate,skipped=skipped,queries=q,widths=list(widths),
                coset_pairs=copies,folded_domain=n,header_bytes=header,expected_bytes=cost)

@lru_cache(None)
def optimize(degree, rate, regime, bits, extension=8, hash_bytes=48):
    # Bound final disclosure to 64 Ext8 coefficients.
    best=(4*extension*degree,[]) if degree<=64 else (float('inf'),[])
    for k in range(1,min(8,degree.bit_length()-1)+1):
        edge=stage(degree,rate,k,regime,(8*extension,),bits,extension,hash_bytes)
        for nr in RATES:
            nd=degree//(1<<k)
            child,path=optimize(nd,nr,regime,bits,extension,hash_bytes)
            candidate=edge['expected_bytes']+child
            if candidate<best[0]:best=(candidate,[dict(edge,next_rate=nr)]+path)
    return best


def simulate(path,seed,extension=8,hash_bytes=48):
    rng=random.Random(seed);size=0;rows=[]
    for s in path:
        n=s['folded_domain'];samples=[rng.randrange(n) for _ in range(s['queries'])]
        indices={i+j*n for i in samples for j in range(s['coset_pairs'])}
        leaves=len(indices)*sum(s['widths'])
        hashes=frontier(indices,n*s['coset_pairs'])*hash_bytes*len(s['widths'])
        size+=leaves+hashes+s['header_bytes']
        rows.append(dict(leaf_bytes=leaves,hash_bytes=hashes))
    last=path[-1];terminal=last['degree']//(1<<last['skipped'])
    return dict(bytes=size+4*extension*terminal,terminal_degree=terminal,stages=rows)


def main():
    checks=0
    for n in (2,4,8):
        for q in (1,2,3):
            ts=list(itertools.product(range(n),repeat=q))
            exact=(F(sum(len(set(t)) for t in ts),len(ts)),
                   F(sum(frontier(t,n) for t in ts),len(ts)))
            assert all(abs(a-float(b))<1e-10 for a,b in zip(geometry(n,q),exact))
            for copies in (1,2,4):
                for t in ts[:32]:
                    ids={i+j*n for i in t for j in range(copies)}
                    assert frontier(ids,n*copies)==copies*frontier(t,n)
                    checks+=1
    results=[]
    for regime,bits in itertools.product(('current','unique','johnson'),BUDGETS):
        candidates=[]
        # Equal source degrees avoid assuming a heterogeneous multi-fold extraction.
        for packing in (16,32,64,128,256):
            degree=256*packing
            widths=tuple(8*((w+packing-1)//packing) for w in (803,424))
            for k in range(1,9):
                edge=stage(degree,4,k,regime,widths,bits)
                for nr in RATES:
                    child,path=optimize(degree//(1<<k),nr,regime,bits)
                    fixed=8+96*(degree.bit_length()-1)+51328
                    candidates.append(dict(packing=packing,fixed_bytes=fixed,
                        expected_subtotal_bytes=fixed+edge['expected_bytes']+child,
                        path=[dict(edge,next_rate=nr)]+path))
        best=min(candidates,key=lambda c:c['expected_subtotal_bytes'])
        trials=[simulate(best['path'],82601+s) for s in range(16)]
        for trial in trials:trial['subtotal_bytes']=trial['bytes']+best['fixed_bytes']
        results.append(dict(regime=regime,query_bits_per_stage=bits,best=best,trials=trials,
                            min_subtotal_bytes=min(t['subtotal_bytes'] for t in trials),
                            max_subtotal_bytes=max(t['subtotal_bytes'] for t in trials)))
    report=dict(status='CONDITIONAL_WEIGHTED_CODE_SWITCH_GEOMETRY',results=results,
        rates=RATES,isolated_query_bits_per_stage=BUDGETS,exhaustive_geometry_cases=9,
        coset_frontier_checks=checks,
        scope='Retained slice widths803/424 pooled by commitment phase, equal packing, base source paired leaves priced by all lanes; subsequent Ext8 pairs64bytes. '
              'All source coset openings included. Two separate source trees. Scalar terminal disclosure at most64 coefficients. '
              'Fixed bytes include51328 local/GKR plus weighted reduction96logD plus8 framing. '
              'Excludes public envelope and parameters. No grinding. Expected costs with16 simulated schedules. '
              'Repeated weighted code switching and its soundness composition unimplemented/unproved. Unique/Johnson transfer not established for this protocol. '
              'Selected bits apply ONLY to each isolated query term; no algebraic/list/OOD/QROM security claim or gate change.')
    out=Path(__file__).resolve().parents[2]/'results/weighted-code-switch-screen.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    for r in results:
        print(r['regime'],r['query_bits_per_stage'],r['best']['packing'],r['best']['expected_subtotal_bytes'],
              r['min_subtotal_bytes'],r['max_subtotal_bytes'],
              [(s['degree'],s['rate'],s['skipped'],s['next_rate'],s['queries']) for s in r['best']['path']])

if __name__=='__main__':main()
