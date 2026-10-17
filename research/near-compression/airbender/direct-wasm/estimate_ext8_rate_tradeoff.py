"""Conditional rate/size tradeoff under existing abstract replay inequality.
No claim that alternate rates are implemented or composed/QROM certified.
"""
import json,random,argparse
from fractions import Fraction as F
from pathlib import Path
from estimate_ext8_multiproof_geometry import frontier
P=2013265921
def parameters(D,B):
    N=B*D;T=(2*N+D)//3+1;E=N-B
    q=1
    while F(E,P**8)+F(T-1,N)**q>F(1,2**130):q+=1
    assert 2*N+D<3*T
    assert q==1 or F(E,P**8)+F(T-1,N)**(q-1)>F(1,2**130)
    return N,T,E,q

def measure(D,B,q,seed):
    rng=random.Random(seed)
    samples=[rng.randrange(B*D) for _ in range(q)]
    d=D;total=(D.bit_length()-1)*144+80
    while d>1:
        count=B*d//2;indices={s%count for s in samples}
        total+=len(indices)*(8 if d==D else 64)+48*frontier(indices,count)
        d//=2
    return total
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();rows=[]
    for D in (131072,262144):
        for B in (4,8,16,32,64,128):
            N,T,E,q=parameters(D,B);assert N<=2**27
            sizes=[measure(D,B,q,s) for s in range(8)]
            rows.append(dict(degree=D,blowup=B,domain=N,threshold=T,extraction_numerator=E,queries=q,min_bytes=min(sizes),max_bytes=max(sizes),mean_bytes=sum(sizes)/8))
    r=dict(status='conditional parameter arithmetic and geometry simulation',rows=rows,target_replay_bits=130,field_degree=8,threshold_rule='T=floor((2N+D)/3)+1',extraction_rule='E=sum(next-domain-sizes)=N-B for binary folds and B>=4',limits=['Only rate4 runtime profile exists; alternate domains are hypothetical instantiations of abstract geometric premises.','Size includes scalar leaf/frontier/round data only; no config/framing/upstream/fullNEAR.','Ideal replay bound only; adversarial-root extraction, FS/QROM and total security budget open.','Deterministic query simulation, not actual proof measurements or universal lower bounds.'])
    a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(rows,indent=2))
