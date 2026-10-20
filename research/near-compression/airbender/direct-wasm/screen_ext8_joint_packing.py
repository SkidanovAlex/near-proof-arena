"""Counterfactual packing/group geometry with an enforced shared use root."""
import argparse,gzip,hashlib,json,random
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from estimate_ext8_multiproof_geometry import frontier
from screen_ext8_grouped_geometry import minimum_queries


class Costs:
    def __init__(self,samples,logB):self.samples=samples;self.logB=logB
    @lru_cache(None)
    def stats(self,logcount):
        assert logcount>=0
        count=1<<logcount;indices={s%count for s in self.samples}
        return len(indices),48*frontier(indices,count)
    def opening(self,logcount,width):
        unique,auth=self.stats(logcount);return unique*width+auth
    def source(self,rowlog,width,packlog,Dlog,k):
        logd=rowlog+packlog;leafbits=max(1,k-Dlog+logd)
        lanes=(width+(1<<packlog)-1)//(1<<packlog)
        return self.opening(self.logB+logd-leafbits,4*(1<<leafbits)*lanes),leafbits,lanes
    @lru_cache(None)
    def tail(self,logd):
        if logd==0:return 0,[]
        choices=[]
        for k in range(1,min(4,logd)+1):
            rest,path=self.tail(logd-k)
            choices.append((self.opening(self.logB+logd-k,32*(1<<k))+48+rest,[k]+path))
        return min(choices,key=lambda x:x[0])


def optimize(shapes,use,logB,large,small,*,max_domain_log=27):
    comp=Costs(large,logB);call=Costs(small,logB)
    caps=[(width-1).bit_length() for _,width in shapes];candidates=[]
    for Dlog in range(max(n for n,_ in shapes),min(max(n+p for (n,_),p in zip(shapes,caps)),max_domain_log-logB)+1):
        for k in range(1,min(4,Dlog)+1):
            choices=[]
            for j,(rowlog,width) in enumerate(shapes):
                opts=[]
                for packlog in range(min(caps[j],Dlog-rowlog)+1):
                    cost,leafbits,lanes=comp.source(rowlog,width,packlog,Dlog,k)
                    opts.append(dict(cost=cost,packing=1<<packlog,log_degree=rowlog+packlog,leaf_bits=leafbits,lanes=lanes))
                choices.append(opts)
            best=[min(opts,key=lambda x:x['cost']) for opts in choices]
            for use_choice in choices[use]:
                chosen=list(best);chosen[use]=use_choice
                if not any(x['log_degree']==Dlog for x in chosen):
                    forced=[]
                    for j,opts in enumerate(choices):
                        if j==use:continue
                        for x in opts:
                            if x['log_degree']==Dlog:forced.append((x['cost']-chosen[j]['cost'],j,x))
                    if not forced:continue
                    _,j,x=min(forced,key=lambda x:x[0]);chosen[j]=x
                callD=use_choice['log_degree'];callk=use_choice['leaf_bits']
                if callk>min(4,callD):continue
                n,w=shapes[use];packlog=use_choice['packing'].bit_length()-1
                call_source,callbits,_=call.source(n,w,packlog,callD,callk)
                assert callbits==use_choice['leaf_bits']
                rest,path=comp.tail(Dlog-k);cr,cp=call.tail(callD-callk)
                compression=40+192*Dlog+48+rest+sum(x['cost'] for x in chosen)
                calls=40+192*callD+48+cr+call_source
                candidates.append(dict(opening_bytes=compression+calls,compression_opening_bytes=compression,call_opening_bytes=calls,
                    degree=1<<Dlog,compression_groups=[k]+path,call_groups=[callk]+cp,branches=chosen,
                    shared_use_layout=dict(row_log=n,width=w,packing=use_choice['packing'],blowup=1<<logB,leaf_bits=callbits)))
    return min(candidates,key=lambda x:x['opening_bytes'])


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--pool-phases',action='store_true');a=p.parse_args()
    package=Path(__file__).resolve().parents[2];source=package/'results/ext8-compression-q309/prover-report.json.gz'
    report=json.loads(gzip.decompress(source.read_bytes()))
    shapes=[(report['source_rows'][b['table']].bit_length()-1,b['width']) for b in report['opening_branches']]
    use=next(i for i,b in enumerate(report['opening_branches']) if b['table']==3 and b['branch']==0)
    original_cells=sum((1<<n)*w for n,w in shapes)
    fixed=143469;records=[]
    if a.pool_phases:
        source_shapes=[shapes[i] for i,b in enumerate(report['opening_branches']) if b['branch']==0 and i!=use]
        aux_shapes=[shapes[i] for i,b in enumerate(report['opening_branches']) if b['branch']==1]
        pooled=[(max(n for n,_ in group),sum(w for _,w in group)) for group in (source_shapes,aux_shapes)]
        fixed-=48*(len(shapes)-3)
        shapes=pooled+[shapes[use]];use=2

    for bits in (128,220):
        for logB in (2,4,6,8):
            B=1<<logB
            for regime,factor in [('current',Fraction(2*B+1,3*B)),('upstream_unique',Fraction(B+1,2*B)),('upstream_johnson',Fraction(21,20*(1<<(logB//2))))]:
                q=minimum_queries(factor,bits);runs=[]
                for seed in range(4):
                    rng=random.Random(902000+seed);large=[rng.randrange(1<<27) for _ in range(q)];small=[rng.randrange(1<<27) for _ in range(q)]
                    best=optimize(shapes,use,logB,large,small);best.update(seed=seed,combined_bytes=fixed+best['opening_bytes']);runs.append(best)
                records.append(dict(query_union_target_bits=bits,blowup=B,regime=regime,queries=q,min_bytes=min(x['combined_bytes'] for x in runs),max_bytes=max(x['combined_bytes'] for x in runs),runs=runs))
    result=dict(status='COUNTERFACTUAL_SHARED_ROOT_CONSTRAINED_SEARCH',phase_pooling=a.pool_phases,original_cells=original_cells,modeled_cells=sum((1<<n)*w for n,w in shapes),shapes=shapes,use_branch=use,fixed_bytes=fixed,records=records,
        scope='Geometry optimizer over per-source power-of-two packing up to next power covering width, groups1..4, base-field domains<=2^27. Shared use table has identical packing/domain/coset leaf size in compression and call proofs; contexts must encode this layout. Optional pooling keeps the external use root separate and pools other sources/auxiliaries in their respective transcript phases. Short tables require repeated-row embeddings; their algebraic binding is not implemented or proved here. Code switching absent. Runtime degree/lane caps are not imposed. Fixed upstream overhead retained. Query-only budgets exclude field/local/GKR/bus/extraction/hash/QROM errors;220bits is not a quantum conversion. No implemented proof-size or security claim.',
        hashes={str(x.relative_to(package)):hashlib.sha256(x.read_bytes()).hexdigest() for x in [Path(__file__),source]})
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    for bits in (128,220):
        best=min((r for r in records if r['query_union_target_bits']==bits),key=lambda r:r['min_bytes'])
        print(bits,best['regime'],best['blowup'],best['queries'],best['min_bytes'],best['max_bytes'])

if __name__=='__main__':main()
