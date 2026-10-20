"""Independent full-domain/coefficient checks of code-switch algebra."""
import argparse,json,random
from pathlib import Path
import pq384_ext8_reference as f
import ext8_code_switch_functional as s


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    rng=random.Random(928716);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    cases=[];negatives=[];residual_checks=0
    for log in range(1,8):
        coeff=[scalar() for _ in range(1<<log)];N=4*len(coeff);omega=pow(31,(f.P-1)//N,f.P)
        source=f.fft(coeff+[f.ZERO]*(N-len(coeff)),omega)
        for k in range(1,min(log,4)+1):
            challenges=[scalar() for _ in range(k)];folded=coeff
            for r in challenges:folded=f.affine_fold(folded,r)
            size=1<<k;root=pow(omega,N//size,f.P)
            # Full-domain oracle folding independently of queried coset extraction.
            oracle=source;domain_root=omega
            for r in challenges:
                half=len(oracle)//2
                oracle=[f.add(f.scale(f.add(oracle[j],oracle[j+half]),pow(2,-1,f.P)),f.mul(r,
                    f.sub(f.scale(f.sub(oracle[j],oracle[j+half]),pow(2*pow(domain_root,j,f.P),-1,f.P)),
                          f.scale(f.add(oracle[j],oracle[j+half]),pow(2,-1,f.P))))) for j in range(half)]
                domain_root=domain_root*domain_root%f.P
            points=[];answers=[]
            for index in sorted({0,1,N//size-1,rng.randrange(N//size)}):
                x=pow(omega,index,f.P);values=[source[index+j*(N//size)] for j in range(size)]
                value=s.fold_coset(values,x,root,challenges);point=f.base(pow(x,size,f.P))
                assert value==oracle[index]==f.evaluate(folded,point)
                points.append(point);answers.append(value)
            # New RS encoding can use a different blowup without changing coefficients.
            newN=16*len(folded);newroot=pow(31,(f.P-1)//newN,f.P)
            encoded=f.fft(folded+[f.ZERO]*(newN-len(folded)),newroot)
            for j in (0,1,newN-1):assert encoded[j]==f.evaluate(folded,f.base(pow(newroot,j,f.P)))
            # Include an extension-field OOD evaluation, then mix all constraints.
            z=scalar();points.append(z);answers.append(f.evaluate(folded,z))
            weights=[scalar() for _ in folded];claim=s.dot(folded,weights);mixers=[scalar() for _ in points]
            nw,nc=s.inject(weights,claim,points,answers,mixers);assert s.dot(folded,nw)==nc
            # Residual identity on arbitrary wrong claims/answers, not just honest data.
            badclaim=f.add(claim,f.ONE);badanswers=[f.add(v,scalar()) for v in answers]
            nw,nc=s.inject(weights,badclaim,points,badanswers,mixers)
            residual=f.sub(s.dot(folded,weights),badclaim)
            for pt,ans,mix in zip(points,badanswers,mixers):residual=f.add(residual,f.mul(mix,f.sub(f.evaluate(folded,pt),ans)))
            assert f.sub(s.dot(folded,nw),nc)==residual;residual_checks+=1
            cases.append(dict(log_degree=log,fold_bits=k,queries=len(points)-1,new_blowup=16))
    def reject(name,fn):
        try:fn()
        except ValueError:negatives.append(name)
        else:raise AssertionError(name)
    reject('bad-coset-shape',lambda:s.fold_coset([f.ONE],1,f.P-1,[f.ONE]))
    reject('zero-anchor',lambda:s.fold_coset([f.ONE,f.ONE],0,f.P-1,[f.ONE]))
    reject('nonprimitive-root',lambda:s.fold_coset([f.ONE,f.ONE],1,1,[f.ONE]))
    reject('noncanonical-value',lambda:s.fold_coset([[f.P]*8],1,1,[]))
    reject('mixer-count',lambda:s.inject([f.ONE],f.ONE,[f.ONE],[f.ONE],[]))
    reject('empty-functional',lambda:s.inject([],f.ZERO,[],[],[]))
    reject('dot-shape',lambda:s.dot([f.ONE],[]))
    # Explicit witness that adjacent coefficient-style folding of RS leaves is wrong.
    coeff=[f.base(x) for x in (1,2,3,4)];root=pow(31,(f.P-1)//4,f.P);rs=[f.base(5),f.base(7)]
    values=[f.evaluate(coeff,f.base(pow(root,j,f.P))) for j in range(4)]
    correct=s.fold_coset(values,1,root,rs);naive=f.affine_fold(f.affine_fold(values,rs[0]),rs[1])[0]
    assert correct!=naive
    # A fixed wrong claim plus wrong answer can cancel at one mixer: exhibit it.
    weights=[f.ONE]*len(coeff);honest=s.dot(coeff,weights);point=f.base(3)
    badclaim=f.add(honest,f.base(2));answer=f.add(f.evaluate(coeff,point),f.base(5))
    unique=f.scale(f.inv(f.base(5)),f.P-2)
    mixed,claim=s.inject(weights,badclaim,[point],[answer],[unique])
    assert s.dot(coeff,mixed)==claim
    mixed,claim=s.inject(weights,badclaim,[point],[answer],[f.add(unique,f.ONE)])
    assert s.dot(coeff,mixed)!=claim
    result=dict(unique_cancellation_witness=unique,status='PASS',cases=cases,residual_checks=residual_checks,negative_cases=negatives,adjacent_leaf_counterexample=dict(correct=correct,naive=naive),scope='Algebra-only reference; no new PCS proof, transcript, extraction, proximity or QROM/security claim.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status=result['status'],cases=len(cases),residual_checks=residual_checks,negative_cases=negatives)))

if __name__=='__main__':main()
