"""Geometry-only transport estimate, NOT a proof or security certificate.

Deterministic simulated uniform queries. Each tree transmits unique opened
leaves and its minimal sibling frontier; indices derive from transcript queries.
All query checks retained. Hashes never merged across tree domains.
"""
import argparse,json,random
from pathlib import Path

def frontier(indices,leaves):
    assert leaves>0 and leaves&(leaves-1)==0
    current=set(indices);assert all(0<=i<leaves for i in current)
    count=0
    while leaves>1:
        count+=sum((i^1) not in current for i in current)
        current={i//2 for i in current};leaves//=2
    return count

def measure(D,q,seed):
    rng=random.Random(seed);samples=[rng.randrange(4*D) for _ in range(q)]
    levels=[];degree=D;stage=0
    while degree>=1:
        indices={s%(2*degree) for s in samples}
        # Final constant oracle can be regenerated from disclosed terminal;
        # this estimate therefore transmits no final-tree opening payload.
        hashes=frontier(indices,2*degree) if degree>1 else 0
        leaf_bytes=len(indices)*(8 if stage==0 else 64) if degree>1 else 0
        levels.append(dict(degree=degree,unique_openings=len(indices),frontier_hashes=hashes,leaf_bytes=leaf_bytes,hash_bytes=48*hashes))
        degree//=2;stage+=1
    rounds=D.bit_length()-1
    # Quadratics:3 Ext8; next roots:48; terminal Ext8:32; source root:48.
    fixed=rounds*(3*32+48)+32+48
    leaves=sum(r['leaf_bytes'] for r in levels);hashes=sum(r['hash_bytes'] for r in levels)
    return dict(seed=seed,source_degree=D,queries=q,fixed_bytes=fixed,leaf_bytes=leaves,frontier_hash_bytes=hashes,estimated_payload_bytes=fixed+leaves+hashes,levels=levels)

def run():
    # Exact tiny-tree sanity checks include dense opening and scattered paths.
    assert frontier([],8)==0 and frontier([0],8)==3
    assert frontier([0,1],8)==2 and frontier([0,7],8)==4
    assert frontier(range(8),8)==0
    rows=[measure(D,314,s) for D in [32,1024,131072,262144] for s in range(8)]
    summary=[]
    for D in [32,1024,131072,262144]:
        rs=[r for r in rows if r['source_degree']==D];sizes=[r['estimated_payload_bytes'] for r in rs]
        summary.append(dict(degree=D,queries=314,min_bytes=min(sizes),max_bytes=max(sizes),mean_bytes=sum(sizes)/len(sizes),all_below_300000=all(x<300000 for x in sizes)))
    return dict(status='geometry simulation, not measured proof',summary=summary,samples=rows,assumptions=['Scalar source paired leaves are8bytes; every fold paired leaf64bytes; SHA384digest48bytes.','Optimal per-tree sibling frontier, no cross-tree dedup; all314 checks retained.','Terminal constant tree regenerated; transcript-derived indices omitted.','Fixed overhead includes round quadratics/roots, source root and terminal only.'],excluded=['Actual framing/config/public statement bytes and codec bounds.','GKR, joint-source reduction, recursion, AIR, NEAR state transition witness/proof.','FS/QROM and upstream security budget; deterministic PRNG is simulation only.'],interpretation='These are simulated achievable payload component counts for an ideal frontier codec, not measured implementations or lower bounds on other protocols.')
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();r=run();a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r['summary'],indent=2))
