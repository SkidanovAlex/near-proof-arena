"""Frozen-verifier SWIRL geometry screen with Merkle frontier estimates.

Conditional query accounting only. Column reduction is free; its implementation,
all other soundness terms and PQ hash instantiation remain open.
"""
import functools
import hashlib
import itertools
import json
import math
import random
from fractions import Fraction as F
from pathlib import Path

from screen_swirl_query_payload import mass_bounds, minimal_queries

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'results/swirl-security-review/stacking-geometry'


def frontier_size(indices, depth):
    nodes = set(indices)
    count = 0
    for _ in range(depth):
        count += sum((i ^ 1) not in nodes for i in nodes)
        nodes = {i // 2 for i in nodes}
    return count


def expected_frontier(depth, q):
    total = 0.0
    for level in range(1, depth+1):
        nodes = 1 << level
        one_empty = math.exp(q*math.log1p(-1/nodes))
        pair_empty = 0 if nodes == 2 else math.exp(q*math.log1p(-2/nodes))
        total += nodes*(one_empty-pair_empty)
    return total


@functools.lru_cache(None)
def queries(log_rate, domain):
    lo, hi = mass_bounds(log_rate, domain)
    return minimal_queries(lo,hi,F(1,2**257))


def cost(cells, cached, height, log_rate, fold, terminal, extension, digest,
         supplied_queries=None, remove_columns=True, public_cached=False):
    rounds = (height-terminal+fold-1)//fold
    final_log = height-rounds*fold
    assert rounds > 0 and final_log >= 0 and height+log_rate <= 27
    widths = [(n+(1<<height)-1)//(1<<height) for n in (cells,cached)]
    if public_cached:
        widths = widths[:1]
    trees = len(widths)
    domains = [height+log_rate-fold-r for r in range(rounds)]
    qs = supplied_queries or [queries(log_rate+r*(fold-1),d) for r,d in enumerate(domains)]
    assert len(qs)==rounds and min(domains)>0
    # Exact fixed-layout message counts, calibrated to the retained root proof.
    fixed_ext = 715+159+(0 if remove_columns else 2694)
    fixed_ext += 7+2*(height-2)+sum(widths)  # stacking
    fixed_ext += 2*fold*rounds+(rounds-1)+(1<<final_log)
    fixed_base = 2+fold*rounds+rounds
    framing = 885+4*(rounds-3)-4*int(public_cached)
    fixed = framing+4*fixed_base+4*extension*fixed_ext+digest*(rounds-1+trees)
    values = []
    for r,q in enumerate(qs):
        values.append(q*(1<<fold)*(4*sum(widths) if r==0 else 4*extension))
    path_hashes = sum(q*d*(trees if r==0 else 1) for r,(q,d) in enumerate(zip(qs,domains)))
    frontier_hashes = sum(expected_frontier(d,q)*(trees if r==0 else 1)
                          for r,(q,d) in enumerate(zip(qs,domains)))
    # Query values are charged per draw, even if a draw repeats. Frontier only
    # deduplicates authentication. Thus the codecs being compared are explicit.
    return dict(height=height,log_rate=log_rate,fold=fold,terminal_max=terminal,
                final_log=final_log,rounds=rounds,widths=widths,domains=domains,
                queries=qs,extension=extension,digest_bytes=digest,
                public_cached=public_cached, fixed_bytes=fixed,query_value_bytes=sum(values),
                raw_paths_bytes=fixed+sum(values)+digest*path_hashes,
                expected_frontier_bytes=fixed+sum(values)+digest*frontier_hashes,
                expected_frontier_hashes=frontier_hashes)


def main():
    # Exhaustive independent check: all with-replacement query sequences.
    checked = 0
    for depth in (1,2,3):
        for q in (1,2,3):
            seqs = list(itertools.product(range(1<<depth),repeat=q))
            actual = sum(frontier_size(s,depth) for s in seqs)/len(seqs)
            assert math.isclose(actual,expected_frontier(depth,q),abs_tol=1e-10)
            checked += len(seqs)
    source_path = ROOT/'results/swirl-security-review/chain/report.json'
    source_bytes = source_path.read_bytes()
    chain = json.loads(source_bytes)
    root = chain['records'][-1]
    cells,cached = root['common_cells'],root['cached_cells']
    baseline = cost(cells,cached,20,4,4,10,4,32,[61,30,20],False)
    assert baseline['raw_paths_bytes']==root['serialized_bytes']==242809
    records=[]
    for extension,digest,public_cached in itertools.product((9,12),(52,64),(False,True)):
        options=[]
        for height in range(15,26):
            for log_rate in range(2,28-height):
                for fold in range(1,9):
                    for terminal in range(1,13):
                        rounds=(height-terminal+fold-1)//fold
                        if height-rounds*fold<0: continue
                        options.append(cost(cells,cached,height,log_rate,fold,terminal,extension,digest,
                                            public_cached=public_cached))
        best=min(options,key=lambda x:x['expected_frontier_bytes'])
        rng = random.Random(20261017)
        samples = []
        for _ in range(16):
            hashes = sum(frontier_size([rng.randrange(1<<d) for _ in range(q)],d) *
                         ((1 if public_cached else 2) if r==0 else 1)
                         for r,(d,q) in enumerate(zip(best['domains'],best['queries'])))
            samples.append(best['fixed_bytes']+best['query_value_bytes']+digest*hashes)
        best['sample_min_bytes'], best['sample_max_bytes'] = min(samples),max(samples)
        records.append(dict(extension=extension,digest_bytes=digest,public_cached=public_cached,
                            screened=len(options),best=best,
                            optimistic_size_survivors=sum(x['expected_frontier_bytes']<300000 for x in options)))
        print(json.dumps(records[-1]))
    chosen = next(r['best'] for r in records if r['extension']==9 and r['digest_bytes']==52 and r['public_cached'])
    workload_sensitivity = [dict(divisor=divisor, **cost((cells+divisor-1)//divisor,cached,
        chosen['height'],chosen['log_rate'],chosen['fold'],chosen['terminal_max'],9,52,public_cached=True))
        for divisor in (1,2,4,8)]
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'report.json').write_text(json.dumps(dict(status='OPTIMISTIC_GEOMETRY_SCREEN',
        source_report_sha256=hashlib.sha256(source_bytes).hexdigest(),
        baseline=baseline,frontier_exhaustive_sequences=checked,records=records,
        workload_sensitivity=workload_sensitivity,
        security_certified=False,scope='Frozen measured verifier, free column reduction, C=1 Q=2^128, no grinding credit, each query term independently granted full1/2 budget. Expected frontier size is not a deterministic bound.',
        exclusions=['Column-reduction proof and altered verifier workload',
                    'PCS proximity/list/algebraic errors','Hash security and quantum compiler',
                    'NEAR/VM binding and stabilized recursion keys', 'Public-cache variant grants all cached evaluation and binding work free', 'Workload reductions are hypothetical, not implemented']),indent=2)+'\n')


if __name__=='__main__':
    main()
