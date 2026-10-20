"""Fixed-query packing/pooling geometry screen, calibrated to an actual codec.
No security change is inferred from equal query counts. Candidate geometry
still needs implementation and soundness-parameter revalidation.
"""
import argparse, hashlib, json, random
from itertools import product
from estimate_ext8_rate_tradeoff import parameters
from pathlib import Path
import pq384_multiproof as mp
import pq384_ext8_weighted as pcs

def tree_cost(half,samples,width):
    indices=[s%half for s in samples]
    return dict(leaf_bytes=len(set(indices))*width,authentication_bytes=48*len(mp.boundary(half,indices)))
def total(cost):return cost['leaf_bytes']+cost['authentication_bytes']
def cost(rows,width,packing,samples,blowup=4):
    d=rows*packing;result=tree_cost(blowup*d//2,samples,8*((width+packing-1)//packing))
    return dict(packing=packing,degree=d,lanes=(width+packing-1)//packing,**result)
def fold_cost(D,samples,blowup=4):
    result=dict(leaf_bytes=0,authentication_bytes=0);half=blowup*D//4
    while half>blowup//2:
        c=tree_cost(half,samples,64)
        for key in result:result[key]+=c[key]
        half//=2
    return result

def choose(widths,rows,D,samples,blowup=4):
    choices=[]
    for width in widths:
        choices.append([cost(rows,width,1<<k,samples,blowup) for k in range(11)
            if rows*(1<<k)<=D and (width+(1<<k)-1)//(1<<k)<=64])
    if any(not c for c in choices):return None
    # Fix each possible branch attaining D; others can independently minimize.
    best=None
    for anchor in range(len(widths)):
        allowed=[c for c in choices[anchor] if c['degree']==D]
        if not allowed:continue
        selected=[min(c,key=total) for c in choices];selected[anchor]=min(allowed,key=total)
        score=sum(map(total,selected))
        if best is None or score<best[0]:best=(score,selected)
    return best

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--capture',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    cfg=json.loads((args.capture/'opening.json').read_text());proof=json.loads((args.capture/'proof.json').read_text())
    ds,D,_,_,_,_,_,samples=pcs.replay(proof,bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'],queries=cfg['queries'])
    assert pcs.verify(proof,bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']),cfg['branches'],cfg['claim'],queries=cfg['queries'])
    baseline=sum(total(tree_cost(2*d,samples,8*len(b['lanes']))) for b,d in zip(cfg['branches'],ds))+total(fold_cost(D,samples))+8+240*(D.bit_length()-1)+32
    measured=(args.capture/'proof.bin').stat().st_size;assert baseline==measured
    branches=cfg['branches'];assert len(branches)==4 and len(set(b['log_rows'] for b in branches))==1
    rows=1<<branches[0]['log_rows'];widths=[b['width'] for b in branches]
    plans={'separate':widths,'pooled_by_commitment_phase':[widths[0]+widths[2],widths[1]+widths[3]]}
    brute_checks=0
    for d in (4,8,16,32):
        sample=[0,1,3,7];options=[[cost(2,w,1<<k,sample) for k in range(5) if 2*(1<<k)<=d] for w in (3,5)]
        brute=min(sum(map(total,pair)) for pair in product(*options) if max(x['degree'] for x in pair)==d)
        assert choose([3,5],2,d,sample)[0]==brute;brute_checks+=1
    records=[]
    for seed in range(16):
        for profile,ws in plans.items():
            candidates=[]
            for exponent in range(11):
                d=rows*(1<<exponent);rng=random.Random(82301+seed*100+exponent)
                queries=[rng.randrange(4*d) for _ in range(cfg['queries'])]
                selected=choose(ws,rows,d,queries)
                if selected is None:continue
                source_bytes,selection=selected;fold=fold_cost(d,queries);header=8+240*(d.bit_length()-1)+32
                candidates.append(dict(degree=d,packing=[x['packing'] for x in selection],lanes=[x['lanes'] for x in selection],
                    source_bytes=source_bytes,fold_bytes=total(fold),metadata_bytes=header,
                    opening_bytes=source_bytes+total(fold)+header))
            best=min(candidates,key=lambda c:c['opening_bytes']);records.append(dict(seed=seed,profile=profile,best=best,candidates=candidates))
    summaries=[]
    for name in plans:
        results=[r['best'] for r in records if r['profile']==name];sizes=[r['opening_bytes'] for r in results]
        summaries.append(dict(profile=name,min_opening_bytes=min(sizes),max_opening_bytes=max(sizes),mean_opening_bytes=sum(sizes)/len(sizes),
            min_with_local_gkr_scalars=min(sizes)+51328,best=min(results,key=lambda r:r['opening_bytes'])))
    rates=[]
    for blowup in (4,8,16,32,64,128):
        bests=[]
        for seed in range(8):
            candidates=[]
            for exponent in range(11):
                degree=rows*(1<<exponent);domain,threshold,E,q=parameters(degree,blowup)
                if domain>1<<27:continue
                rng=random.Random(82401+seed*100+exponent)
                samples=[rng.randrange(domain) for _ in range(q)]
                selected=choose(plans['pooled_by_commitment_phase'],rows,degree,samples,blowup)
                if selected is None:continue
                source_bytes,selection=selected;fold=fold_cost(degree,samples,blowup);header=8+240*(degree.bit_length()-1)+32
                candidates.append(dict(degree=degree,blowup=blowup,queries=q,threshold=threshold,extraction_numerator=E,
                    packing=[x['packing'] for x in selection],opening_bytes=source_bytes+total(fold)+header))
            bests.append(min(candidates,key=lambda c:c['opening_bytes']))
        sizes=[x['opening_bytes'] for x in bests]
        rates.append(dict(blowup=blowup,min_bytes=min(sizes),max_bytes=max(sizes),mean_bytes=sum(sizes)/len(sizes),best=min(bests,key=lambda c:c['opening_bytes'])))
    report=dict(rate_screen=rates,rate_scope='Conditional PCS-only130-ideal-bit inequality from estimate_ext8_rate_tradeoff; not composed or QROM certification. Alternate rates unimplemented.',brute_force_optimizer_checks=brute_checks,status='CALIBRATED_GEOMETRY_SCREEN' ,queries=cfg['queries'],measured_baseline_bytes=measured,calibrated_baseline_bytes=baseline,
        fixed_hash_bytes=48,fixed_fold_scalar_bytes=32,seed_count=16,summary=summaries,records=records,
        capture_sha256={name:hashlib.sha256((args.capture/name).read_bytes()).hexdigest() for name in ('opening.json','proof.json','proof.bin')},
        scope='Exact codec geometry on retained transcript, then simulated uniform queries for candidate packing. Pooling groups only pre-bus sources and post-bus auxiliaries separately; equal row counts. Queries309/hash384/Ext8/LDE4/binary folding held fixed. Candidate layouts unimplemented; field/degree/PCS bounds need revalidation. Excludes envelope overhead and is not a lower bound for other protocols or a quantum security certificate.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(packing=summaries,rates=rates),indent=2))
if __name__=='__main__':main()
