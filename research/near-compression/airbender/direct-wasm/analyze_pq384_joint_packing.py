"""Exact expected Q8 cost sweep, conditioning on common maximum degree.

Uniform projected queries with replacement; cross-tree independence unnecessary.
Not a secure-query recommendation. Actual deterministic transcripts vary.
"""
import argparse,json,sys
from fractions import Fraction
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--statement',required=True);p.add_argument('--output',required=True)
    a=p.parse_args();sys.path.append(a.reference_dir)
    from estimate_joint_source_cost import expected_counts,validate
    import pq384_global_bus as bus
    spec=json.loads(Path(a.statement).read_text())['spec'];bus.validate(spec);branches=[]
    for ti,t in enumerate(spec['air']['tables']):
        for name,w,key in [('source',t['width'],'source_packings'),('auxiliary',4*bus.aux.layout(t)['aux_columns'],'aux_packings')]:
            if w:branches.append(dict(table=ti,branch=name,width=w,log_rows=spec['log_rows'][ti],packing=spec[key][ti]))
    def cost(n,w,p):
        d=(1<<n)*p;lanes=(w+p-1)//p;l,s=expected_counts(2*d,8)
        return l*8*lanes+s*48
    def totals(choices):
        D=max((1<<b['log_rows'])*p for b,p in zip(branches,choices));n=D.bit_length()-1
        source=sum((cost(b['log_rows'],b['width'],p) for b,p in zip(branches,choices)),Fraction(0))
        folds=sum((32*l+48*s for l,s in [expected_counts(D>>j,8) for j in range(n)]),Fraction(0))
        cache=sum(20*((1<<b['log_rows'])*p)*((b['width']+p-1)//p)+192*((1<<b['log_rows'])*p)-48 for b,p in zip(branches,choices))
        return dict(max_degree=D,initial_authentication_expected_bytes=float(source),shared_fold_expected_bytes=float(folds),joint_header_bytes=6+144*n+16,
                    expected_joint_bytes=float(source+folds)+6+144*n+16,
                    padded_coefficient_slots=len(branches)*D,all_source_cache_estimated_bytes=cache)
    candidates=[];seen=set()
    for logcap in range(7,19):
        cap=1<<logcap;choices=[]
        for b in branches:
            valid=[1<<k for k in range(21) if 128<=(1<<b['log_rows'])*(1<<k)<=cap and (b['width']+(1<<k)-1)//(1<<k)<=64]
            if not valid:break
            choices.append(min(valid,key=lambda p:cost(b['log_rows'],b['width'],p)))
        if len(choices)!=len(branches) or tuple(choices) in seen:continue
        seen.add(tuple(choices));entry=totals(choices);entry['packings']=choices;candidates.append(entry)
    baseline=totals([b['packing'] for b in branches]);best=min(candidates,key=lambda c:c['expected_joint_bytes'])
    report=dict(status='PASS',exact_count_exhaustive_cases=validate(),branches=branches,baseline=baseline,optimal=best,candidates=candidates,
                expected_saving_bytes=baseline['expected_joint_bytes']-best['expected_joint_bytes'],
                limitations=['Q8 expected cost only; no secure parameter claim','Packing changes roots, bus challenges and all proof transcripts; requires fresh run',
                             'All roots retain independent authentication; no cross-tree Merkle sharing','Includes single joint fold chain and its reduction/header, excludes retained AIR prefix'])
    Path(a.output).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['baseline','optimal','expected_saving_bytes']},indent=2))

if __name__=='__main__':main()
