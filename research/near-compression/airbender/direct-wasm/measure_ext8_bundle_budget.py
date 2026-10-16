"""Exact conditional PCS union budget for compression plus call profiles.
Instantiates existing ideal fold/source-far bounds; not a protocol certificate.
"""
import argparse,gzip,hashlib,json,math
from fractions import Fraction
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2]
    path=package/'results/ext8-node-batch/statement.json.gz'
    spec=json.loads(gzip.decompress(path.read_bytes()))['spec']
    degrees=[(1<<n)*packing for n,packing in zip(spec['log_rows'],spec['source_packings'])]
    degrees += [(1<<n)*packing for n,packing in zip(spec['log_rows'],spec['aux_packings'])]
    profiles=[];field=2013265921**8
    for name,degree in [('compression',max(degrees)),('calls',(1<<spec['log_rows'][3])*spec['source_packings'][3])]:
        rounds=degree.bit_length()-1;assert degree==1<<rounds
        domain=4*degree;threshold=(2*domain+degree)//3+1
        assert 2*domain+degree<3*threshold and not 2*domain+degree<3*(threshold-1)
        agreement=Fraction(threshold-1,domain);assert agreement==Fraction(3,4)
        fold=sum(max(domain>>(i+1),2) for i in range(rounds))
        far=rounds*max(domain,2)
        profiles.append(dict(name=name,degree=degree,domain=domain,folds=rounds,threshold=threshold,fold_numerator=fold,conditional_far_numerator=far))
    numerator=sum(x['fold_numerator']+x['conditional_far_numerator'] for x in profiles)
    field_term=Fraction(numerator,field)
    def query_term(q):return len(profiles)*Fraction(3,4)**q
    def bound(q):return field_term+query_term(q)
    results=[]
    for q in (309,531):
        results.append(dict(queries_per_proof=q,query_union_exact=str(query_term(q)),query_union_negative_log2=-math.log2(float(query_term(q))),conditional_union_exact=str(bound(q)),conditional_union_negative_log2=-math.log2(float(bound(q))),conditional_union_at_most_2neg128=bound(q)<=Fraction(1,1<<128)))
    targets={}
    for bits in (128,198,220):
        target=Fraction(1,1<<bits)
        if field_term>=target:targets[str(bits)]=None;continue
        q=0
        while bound(q)>target:q+=1
        assert bound(q)<=target and (q==0 or bound(q-1)>target)
        targets[str(bits)]=q
    report=dict(status='CONDITIONAL_IDEAL_BUDGET_ONLY',profiles=profiles,field_size=str(field),field_union_exact=str(field_term),profiles_checked=results,min_queries_per_proof_for_conditional_union=targets,
        assumptions=['Both PCS components satisfy the explicit fixed-snapshot/adaptive-fold premises of CheckedHistoryAcceptance.', 'Each source-far branch satisfies CheckedHistorySource multiaffine batching and no-joint-representative premises; this script does not prove these for the executable protocol.', 'Ideal uniform field challenges and independent uniform queries within each proof; union bound does not assume independence between proofs.'],
        excluded=['Functional reduction, local sumcheck, GKR and bus errors','Complete near/far case coverage and commitment extraction','Hash security and Fiat-Shamir/QROM losses','Full recursion and NEAR1Pgas'],
        scope='Sum of two conditional source-far/fold/query upper bounds. Exceeding a target means this budget does not certify it, not an attack lower bound. Query counts198/220-bit targets are examples, not quantum-security conversions.',
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [Path(__file__),path,package/'NearCompression/CheckedHistorySource.lean',package/'NearCompression/CheckedHistoryAcceptance.lean']})
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(profiles=profiles,query_profiles=results,targets=targets),indent=2))

if __name__=='__main__':main()
