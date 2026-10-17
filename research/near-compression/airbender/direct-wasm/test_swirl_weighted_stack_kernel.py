"""Independent dense checks of arbitrary current/next stacking weights.

Small BabyBear domains only; not an authenticated PCS/sumcheck implementation.
"""
import hashlib,json,random
from pathlib import Path
P=2013265921
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/weighted-stack-kernel'


def omega(log):return pow(31,(P-1)//(1<<log),P)
def eq_uni(log,x,y):
    result=1
    for _ in range(log):
        result=((x+y)*result+(x-1)*(y-1))%P;x=x*x%P;y=y*y%P
    return result*pow(1<<log,-1,P)%P

def eq_cube(x,y):
    assert len(x)==len(y)
    result=1
    for a,b in zip(x,y):result=result*(a*b+(1-a)*(1-b))%P
    return result

def rot_kernel(log,x,y):
    eq=rot=1
    for a,b in reversed(list(zip(x[1:],y[1:]))):
        rot=(a*(1-b)*eq+(1-a)*b*rot)%P
        eq=(a*b+(1-a)*(1-b))*eq%P
    w=omega(log)
    return (eq_uni(log,x[0],y[0]*w%P)*eq+eq_uni(log,x[0],1)*eq_uni(log,y[0]*w%P,1)*(rot-eq))%P

def source_weight(lskip,stack_log,log_height,start,r,u,a,b):
    n=log_height-lskip;lift=max(n,0)
    bits=[(start>>j)&1 for j in range(lskip+lift,stack_log)]
    high=eq_cube(u[1+lift:],bits)
    if n<0:
        local_log=log_height;rp=[pow(r[0],1<<(-n),P)]
        indicator=eq_uni(-n,pow(u[0],1<<log_height,P),1)
    else:local_log=lskip;rp=r[:1+lift];indicator=1
    up=u[:1+lift]
    current=eq_uni(local_log,up[0],rp[0])*eq_cube(up[1:],rp[1:])%P
    return high*indicator*(a*current+b*rot_kernel(local_log,up,rp))%P


def lagrange(domain,x):
    result=[]
    for j,z in enumerate(domain):
        num=den=1
        for k,y in enumerate(domain):
            if k!=j:num=num*(x-y)%P;den=den*(z-y)%P
        result.append(num*pow(den,-1,P)%P)
    return result

def dense_weights(log,point):
    d=[pow(omega(log),i,P) for i in range(1<<log)]
    uni=lagrange(d,point[0]);result=[]
    for bits in range(1<<(len(point)-1)):
        # Deliberately use direct Boolean basis rather than eq_cube.
        factor=1
        for j,r in enumerate(point[1:]):factor=factor*(r if (bits>>j)&1 else 1-r)%P
        result.extend(factor*x%P for x in uni)
    return result


def main():
    rng=random.Random(20261017);checks=0;rotation_differences=0;short_checks=0
    for lskip in (1,2,3):
        stack_log=lskip+3
        for trial in range(8):
            heights=[lskip+2,lskip+1,lskip,max(0,lskip-1),0]
            # Place each source column in its own stacked column for this test,
            # with several aligned starts to test the high-coordinate selector.
            for height in heights:
                span=1<<max(height,lskip);start=rng.randrange((1<<stack_log)//span)*span
                column=[rng.randrange(P) for _ in range(1<<height)]
                a,b=rng.randrange(P),rng.randrange(P)
                r=[rng.randrange(P) for _ in range(1+max(heights)-lskip)]
                local_log=min(height,lskip)
                point=[pow(r[0],1<<max(lskip-height,0),P)]+r[1:1+max(height-lskip,0)]
                eval_weights=dense_weights(local_log,point)
                direct=sum(w*(a*column[j]+b*column[(j+1)%len(column)]) for j,w in enumerate(eval_weights))%P
                stacked=[0]*(1<<stack_log)
                stride=1<<max(lskip-height,0)
                for j,value in enumerate(column):stacked[start+j*stride]=value
                kernel=[]
                for row in range(1<<stack_log):
                    u=[pow(omega(lskip),row% (1<<lskip),P)]+[(row>>j)&1 for j in range(lskip,stack_log)]
                    kernel.append(source_weight(lskip,stack_log,height,start,r,u,a,b))
                assert sum(x*w for x,w in zip(stacked,kernel))%P==direct
                u=[rng.randrange(P) for _ in range(1+stack_log-lskip)]
                interpolated=sum(x*w for x,w in zip(kernel,dense_weights(lskip,u)))%P
                assert interpolated==source_weight(lskip,stack_log,height,start,r,u,a,b)
                wrong=sum(w*(a*column[j]+b*column[(j-1)%len(column)]) for j,w in enumerate(eval_weights))%P
                rotation_differences+=wrong!=direct
                checks+=2;short_checks+=int(height<lskip)
    assert rotation_differences>0 and short_checks>0
    native=json.loads((OUT/'native-oracle.json').read_text())
    assert len(native)==30
    for case in native:
        assert omega(case['l'])==case['omega']
        assert source_weight(case['l'],case['stack'],case['height'],case['start'],
            [13+i*7 for i in range(4)],[23+i*11 for i in range(4)],17,29)==case['value']
    OUT.mkdir(parents=True,exist_ok=True)
    result=dict(status='ARBITRARY_PAIR_STACK_KERNEL_DENSE_PARITY',identity_checks=checks,native_kernel_checks=len(native),
        short_trace_cases=short_checks,wrong_rotation_distinguished=rotation_differences,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        limitations=['Small synthetic base-field domains, not captured native evaluation points.',
                    'No sumcheck proof or commitment authentication.',
                    'No transcript/QROM soundness, Lean kernel proof or full NEAR proof.'])
    (OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))


if __name__=='__main__':main()
