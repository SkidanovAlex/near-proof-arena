#!/usr/bin/env python3
import argparse,json,random,hashlib
from pathlib import Path
import pq384_ext8_reference as e

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--lean-results',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rows=json.loads(args.lean_results.read_text());checks=0
    for row in rows:
        a=e.canonical(row['a']);b=e.canonical(row['b'])
        actual={'add':e.add(a,b),'sub':e.sub(a,b),'mul':e.mul(a,b),'inv':e.inv(a),'pow17':e.power(a,17),'scale':e.scale(a,row['scalar']),'tower_mul':e.mul(a,b)}
        for key,value in actual.items():assert list(value)==row[key],key;checks+=1
    rng=random.Random(3848);fft_checks=0;fold_checks=0
    for n in (2,4,8,16,32):
        a=[tuple(rng.randrange(e.P) for _ in range(8)) for _ in range(n)]
        omega=pow(440564289,(1<<27)//n,e.P)
        assert e.fft(a,omega)==[e.evaluate(a,e.base(pow(omega,i,e.P))) for i in range(n)]
        fft_checks+=n
        w=[tuple(rng.randrange(e.P) for _ in range(8)) for _ in range(n)]
        for r in (e.ZERO,e.ONE,tuple(rng.randrange(e.P) for _ in range(8))):
            aa=e.affine_fold(a,r);ww=e.affine_fold(w,r);dot=e.ZERO
            for x,y in zip(aa,ww):dot=e.add(dot,e.mul(x,y))
            assert e.evaluate(e.quadratic(a,w),r)==dot;fold_checks+=1
    rejects=0
    for a in ([0]*7,[0]*9,[True]+[0]*7,[e.P]+[0]*7,[-1]+[0]*7):
        try:e.canonical(a)
        except ValueError:rejects+=1
        else:raise AssertionError('invalid accepted')
    report=dict(status='PASS',lean_cases=len(rows),lean_operation_comparisons=checks,
      fft_vs_naive_evaluations=fft_checks,quadratic_fold_identities=fold_checks,canonical_rejections=rejects,
      field='existing certified ZkFormal.Algebra.Fp8; x^8=11 flat coordinates',
      scope='reference arithmetic and mixed base-twiddle FFT only; no new PCS wire profile or security certification',
      files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in (Path(__file__),Path(e.__file__),args.lean_results)])
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
