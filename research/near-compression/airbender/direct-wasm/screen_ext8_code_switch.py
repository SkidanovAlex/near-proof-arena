"""Reprice fixed candidate schedules with changing rates and upstream error slots.
This is a source-formula/geometry experiment, NOT WHIR or our protocol soundness.
"""
import argparse,hashlib,json,math,random,subprocess
from fractions import Fraction as F
from pathlib import Path
from estimate_ext8_multiproof_geometry import frontier
P=2013265921
FIELD=P**8
MCA_CONSTANT=F(21**5,48)


def query_count(regime,B,bits):
    target=F(1,1<<bits);q=0
    def fits(n):
        if regime=='upstream_johnson':return F(21,20)**(2*n)/B**n<=target**2
        return F(B+1,2*B)**n<=target
    while not fits(q):q+=1
    assert q==0 or not fits(q-1)
    return q


def slots(regime,D,B,k,nextB,q,bits):
    message=D//(1<<k);target=F(1,1<<bits)
    L=10*B if regime=='upstream_johnson' else 1
    nextL=10*nextB if regime=='upstream_johnson' else 1
    if regime=='upstream_johnson':mca_square=MCA_CONSTANT**2*message**2*B**5/FIELD**2
    else:mca_square=F(message*B,FIELD)**2
    identity=F(2*L,FIELD);choose=nextL*(nextL-1)//2;t=1
    def ood(t):return choose*F(message-1,FIELD)**t
    while ood(t)>target:t+=1
    mixing=F((t+q*(1<<k))*nextL,FIELD)
    # Conservative rational upper bound for a printable additive ledger.
    ceilroot=math.isqrt(B)+(math.isqrt(B)**2!=B)
    mca_upper=MCA_CONSTANT*message*B**2*ceilroot/FIELD if regime=='upstream_johnson' else F(message*B,FIELD)
    errors=dict(mca=mca_upper,identity=identity,ood=ood(t),query=F(1,1<<bits),mixing=mixing)
    checks=dict(mca=mca_square<=target**2,identity=identity<=target,ood=ood(t)<=target,mixing=mixing<=target)
    return t,checks,dict(source_message_length=message,source_list=L,target_list=nextL,mca_bits=-.5*math.log2(float(mca_square)),identity_bits=-math.log2(float(identity)),mixing_bits=-math.log2(float(mixing)),ood_samples=t,conditional_error_upper=str(k*(errors['mca']+identity)+ood(t)+errors['query']+mixing))


def opening(samples,count,width):
    indices={s%count for s in samples}
    return len(indices)*width+48*frontier(indices,count)


def evaluate(shapes,use,run,B,regime,bits,fixed,mode):
    paths=[run['compression_groups'],run['call_groups']]
    # k sumcheck steps each charge MCA and polynomial identity; each switch
    # charges source queries, OOD list separation, and constraint mixing.
    terms=sum(2*sum(path)+3*len(path) for path in paths)
    slot_bits=bits+(terms-1).bit_length();rows=[];total=fixed;bound=F(0);passed=True
    for part,path in enumerate(paths):
        D=run['degree'] if part==0 else 1<<run['branches'][use]['log_degree']
        rate=B;total+=40+96*(D.bit_length()-1) # initial functional reduction + terminal/magic
        rng=random.Random(903000+run['seed']*10+part)
        for stage,k in enumerate(path):
            nxt=rate*(1<<(k-1));nxt=min(nxt,256) if mode=='capped256' else nxt
            q=query_count(regime,rate,slot_bits);t,checks,ledger=slots(regime,D,rate,k,nxt,q,slot_bits)
            samples=[rng.randrange(rate*D//(1<<k)) for _ in range(q)]
            if stage==0:
                selected=range(len(shapes)) if part==0 else [use];data=0
                for j in selected:
                    n,w=shapes[j];pack=run['branches'][j]['packing'];d=(1<<n)*pack
                    leafbits=max(1,k-(D.bit_length()-d.bit_length()))
                    if j==use:assert leafbits==run['shared_use_layout']['leaf_bits']
                    lanes=(w+pack-1)//pack
                    data+=opening(samples,rate*d//(1<<leafbits),4*(1<<leafbits)*lanes)
            else:data=opening(samples,rate*D//(1<<k),32*(1<<k))
            # All quadratic coefficients, next commitment, and actual OOD answers.
            overhead=96*k+48+32*t;total+=data+overhead
            passed=passed and all(checks.values());bound+=F(ledger['conditional_error_upper'])
            rows.append(dict(part=part,stage=stage,degree=D,blowup=rate,next_blowup=nxt,fold_bits=k,queries=q,opening_bytes=data,message_bytes=overhead,checks=checks,**ledger))
            D>>=k;rate=nxt
        assert D==1
    return dict(seed=run['seed'],mode=mode,combined_bytes=total,conditional_slots_pass=passed,conditional_budget_pass=passed and bound<=F(1,1<<bits),slot_bits=slot_bits,charged_terms=terms,conditional_error_upper=str(bound),stages=rows)


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--upstream',type=Path,default=Path('/tmp/nearproof-whir-review-20261016'));a=p.parse_args()
    pin='afec1fac27c1c8cc7331aa5668bc9800f104d92c'
    assert subprocess.check_output(['git','-C',str(a.upstream),'rev-parse','HEAD'],text=True).strip()==pin
    subprocess.run(['git','-C',str(a.upstream),'diff','--exit-code','HEAD','--','src/protocols/params/regime.rs','src/protocols/params/sumcheck.rs','src/protocols/params/code_switch.rs'],check=True,capture_output=True)
    package=Path(__file__).resolve().parents[2];records=[]
    for name in ('joint','pooled'):
        path=package/f'results/ext8-{name}-packing-geometry.json';source=json.loads(path.read_text())
        for r in source['records']:
            if r['regime']=='current':continue # No list-size theorem silently imported for this regime.
            for mode in ('stepping','capped256'):
                runs=[evaluate(source['shapes'],source['use_branch'],x,r['blowup'],r['regime'],r['query_union_target_bits'],source['fixed_bytes'],mode) for x in r['runs']]
                records.append(dict(source_layout=name,target_bits=r['query_union_target_bits'],initial_blowup=r['blowup'],regime=r['regime'],mode=mode,min_bytes=min(x['combined_bytes'] for x in runs),all_conditional_budget_pass=all(x['conditional_budget_pass'] for x in runs),runs=runs))
    upstream=a.upstream/'src/protocols/params'
    result=dict(status='COUNTERFACTUAL_CODE_SWITCH_LEDGER',records=records,upstream_commit='afec1fac27c1c8cc7331aa5668bc9800f104d92c',
        source_formulas={name:hashlib.sha256((upstream/name).read_bytes()).hexdigest() for name in ('regime.rs','sumcheck.rs','code_switch.rs')},
        scope='Reprices existing packing/group schedules; does NOT optimize schedules for changing rates. Rates step by2^(k-1), optionally capped256. Queries recomputed each stage with enough slots for both proofs; OOD samples>=1 chosen from source-formula list separation. SHA384 authentication, Ext8 intermediate values, quadratics, roots, and OOD answers charged. MCA/identity/mixing/OOD checks mirror pinned upstream formulas; no upstream theorem mapping, common candidate extraction, code-switch implementation, whole protocol/FS/QROM certificate or quantum conversion. Field/functional batching outside this hypothetical switch chain remains excluded. mca uses exact squared comparison; reported additive upper bound rounds sqrt(B) upward. Initial roots must be redesigned for selected layouts.',
        files={str(x.relative_to(package)):hashlib.sha256(x.read_bytes()).hexdigest() for x in [Path(__file__),package/'results/ext8-joint-packing-geometry.json',package/'results/ext8-pooled-packing-geometry.json']})
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    for bits in (128,220):
        eligible=[r for r in records if r['target_bits']==bits and r['all_conditional_budget_pass']]
        if eligible:
            best=min(eligible,key=lambda r:r['min_bytes']);print(bits,best['source_layout'],best['regime'],best['mode'],best['initial_blowup'],best['min_bytes'])
        else:print(bits,'NO CONDITIONAL SLOT-PASSING CANDIDATE')

if __name__=='__main__':main()
