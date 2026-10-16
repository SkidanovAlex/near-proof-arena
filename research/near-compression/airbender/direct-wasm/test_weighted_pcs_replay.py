#!/usr/bin/env python3
import argparse,copy,hashlib,json,subprocess,sys
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-directory',type=Path,required=True)
    ap.add_argument('--lean-directory',type=Path,required=True);ap.add_argument('--fixture',type=Path,required=True)
    ap.add_argument('--temporary-olean-directory',type=Path);ap.add_argument('--output-directory',type=Path,required=True)
    a=ap.parse_args();sys.path.insert(0,str(a.reference_directory))
    from verify_whir_toy import P,base,add,sub,mul
    from pq384_joint_opening import eq_weights,equality_weight_at
    from pq384_global_chain import round_start,polynomial
    zero=base(0);one=base(1)
    class Tape:
        seed=b'\0'*48
        def __init__(self,r):self.r=r
        def commit(self,*args):pass
        def draw(self,label,count,coeff):
            assert (label,count,coeff)==(b'fold-challenge',1,4)
            return [list(self.r)],0
    cases=[]
    for n in [0,1,3,8]:
        u=[(i+2,i+3,i+5,i+7) for i in range(n)];rs=[(i+11,i+13,i+17,i+19) for i in range(n)]
        for exceptional in ([False,True] if n else [False]):
            us=list(u);rr=list(rs)
            if exceptional:us[0]=zero;rr[0]=one
            coeff=[(i+23,i+29,i+31,i+37) for i in range(2**n)];weights=eq_weights(us)
            initial=zero
            for c,w in zip(coeff,weights):initial=add(initial,mul(c,w))
            sent=[]
            for r in rr:
                q=[zero,zero,zero]
                for i in range(0,len(coeff),2):
                    da=sub(coeff[i+1],coeff[i]);dw=sub(weights[i+1],weights[i])
                    q[0]=add(q[0],mul(coeff[i],weights[i]))
                    q[1]=add(q[1],add(mul(da,weights[i]),mul(coeff[i],dw)))
                    q[2]=add(q[2],mul(da,dw))
                sent.append(q)
                coeff=[add(coeff[i],mul(r,sub(coeff[i+1],coeff[i]))) for i in range(0,len(coeff),2)]
                weights=[add(weights[i],mul(r,sub(weights[i+1],weights[i]))) for i in range(0,len(weights),2)]
            cases.append(dict(point=us,challenges=rr,sent=sent,initial=initial,terminal=coeff[0]))
    honest_count=len(cases)
    for c in list(cases):
        if c['sent']:
            bad=copy.deepcopy(c);bad['sent'][0][0]=add(bad['sent'][0][0],one);cases.append(bad)
        bad=copy.deepcopy(c);bad['terminal']=add(bad['terminal'],one);cases.append(bad)
        if c['point']:
            bad=copy.deepcopy(c);bad['challenges']=bad['challenges'][:-1];cases.append(bad)
    expected=[]
    for c in cases:
        u,rs,qs=c['point'],c['challenges'],c['sent'];n=len(u);claims=[c['initial']]
        # Lean stores each post-round evaluation independently; endpoint checks chain these values.
        for i in range(n):claims.append(polynomial(qs[i] if i<len(qs) else [zero]*3,rs[i] if i<len(rs) else zero))
        checked=len(rs)==len(qs)==n
        for i in range(n):
            try:round_start(Tape(rs[i] if i<len(rs) else zero),[list(x) for x in qs[i]],claims[i])
            except (ValueError,IndexError):checked=False
        scales=[equality_weight_at(u[:i],(rs+[zero]*n)[:i]) for i in range(n+1)]
        checked=checked and mul(scales[-1],c['terminal'])==claims[-1]
        expected.append(dict(checked=checked,claims=[list(x) for x in claims],scales=[list(x) for x in scales],
          weights=[[list(mul(scales[i],w)) for w in eq_weights(u[i:])] for i in range(n+1)]))
    assert all(x['checked'] for x in expected[:honest_count])
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True);ip=out/'inputs.json';op=out/'lean-results.json'
    ip.write_text(json.dumps(cases));command=['lake','env']
    if a.temporary_olean_directory:
        lp=subprocess.check_output(command+['printenv','LEAN_PATH'],cwd=a.lean_directory,text=True).strip()
        command+=['env','LEAN_PATH='+str(a.temporary_olean_directory)+':'+lp]
    subprocess.run(command+['lean','--run',str(a.fixture),str(ip),str(op)],cwd=a.lean_directory,check=True)
    assert json.loads(op.read_text())==expected
    zero_scale_accepts=sum(x['checked'] for x in expected[honest_count:])
    assert zero_scale_accepts==3
    report=dict(status='PASS',honest_cases=honest_count,total_cases=len(cases),rejected=sum(not x['checked'] for x in expected),
      zero_scale_terminal_mutations_accepted=zero_scale_accepts,
      limits=['Scripted challenge tape isolates actual round_start arithmetic; hash/FS sampling is not claimed.',
              'Zero equality scale intentionally permits any terminal constant in the residual test; root and query checks remain necessary.',
              'No acceptance-to-proximity conclusion without bounding extraction events and query sampling.'],
      files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in [Path(__file__),a.fixture,ip,op,a.reference_directory/'pq384_global_chain.py',a.reference_directory/'pq384_joint_opening.py']])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','limits')}))

if __name__=='__main__':main()
