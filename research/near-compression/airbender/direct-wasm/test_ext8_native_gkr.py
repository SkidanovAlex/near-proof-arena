"""Native GKR rounds checked against independent evaluation at 0,1,2."""
import argparse, ctypes, hashlib, json, random, subprocess, tempfile
from pathlib import Path
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel

def gate(op,a,b):return {'add':f.add,'sub':f.sub,'mul':f.mul}[op](a,b)
def reference(gates,gw,v,folded,axis,bit,a,t):
    total=f.ZERO
    for (op,i,j),w in zip(gates,gw):
        index=(i if axis==0 else j)>>bit
        x,y=folded[index&~1],folded[index|1]
        fv=f.add(x,f.mul(t,f.sub(y,x)))
        eq=t if index&1 else f.sub(f.ONE,t)
        left,right=(fv,v[j]) if axis==0 else (a,fv)
        total=f.add(total,f.mul(f.mul(w,eq),gate(op,left,right)))
    return total

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rng=random.Random(81849)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='ext8-gkr-native-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True)
        k=Kernel(lib);rounds=0;cases=0
        for n in (2,8,32):
            v=[scalar() for _ in range(n)]
            gates=[(op,rng.randrange(n),rng.randrange(n)) for op in ('add','sub','mul') for _ in range(9)]
            for mode in ('zero','one','random'):
                gw=[scalar() for _ in gates];claim=f.ZERO
                for (op,i,j),w in zip(gates,gw):claim=f.add(claim,f.mul(w,gate(op,v[i],v[j])))
                a=f.ZERO
                for axis in (0,1):
                    folded=list(v)
                    for bit in range(n.bit_length()-1):
                        q=k.gkr_round(gates,gw,v,folded,axis,bit,a)
                        for t in (f.ZERO,f.ONE,f.base(2)):
                            assert f.evaluate(q,t)==reference(gates,gw,v,folded,axis,bit,a,t)
                        assert f.add(q[0],f.evaluate(q,f.ONE))==claim
                        r=f.ZERO if mode=='zero' else f.ONE if mode=='one' else scalar()
                        claim=f.evaluate(q,r)
                        gw=[f.mul(w,r if ((i if axis==0 else j)>>bit)&1 else f.sub(f.ONE,r)) for (op,i,j),w in zip(gates,gw)]
                        folded=k.affine_fold(folded,r);rounds+=1
                    if axis==0:a=folded[0]
                expected=f.ZERO
                for (op,_,_),w in zip(gates,gw):expected=f.add(expected,f.mul(w,gate(op,a,folded[0])))
                assert claim==expected;cases+=1
        bad_calls=[lambda:k.gkr_round([('bad',0,1)],[f.ONE],[f.ZERO,f.ONE],[f.ZERO,f.ONE],0,0),
            lambda:k.gkr_round([('add',0,2)],[f.ONE],[f.ZERO,f.ONE],[f.ZERO,f.ONE],0,0),
            lambda:k.gkr_round([],[],[f.ZERO,f.ONE],[f.ZERO],0,0),
            lambda:k.gkr_round([],[],[],[f.ZERO,f.ONE],2,0),
            lambda:k.gkr_round([],[],[],[f.ZERO,f.ONE],0,-1)]
        for call in bad_calls:
            try:call()
            except ValueError:pass
            else:raise AssertionError('bad GKR input accepted')
        gs=(ctypes.c_uint32*3)(3,0,1);w=k.pack([f.ONE]);v=k.pack([f.ZERO,f.ONE]);left=k.pack([f.ZERO]);out=(ctypes.c_uint32*24)(*([77]*24))
        assert k.lib.near_ext8_gkr_round(gs,1,w,v,2,v,2,0,0,left,out)==1
        gs[0]=0;gs[2]=2
        assert k.lib.near_ext8_gkr_round(gs,1,w,v,2,v,2,0,0,left,out)==1
        gs[2]=1;w[0]=f.P
        assert k.lib.near_ext8_gkr_round(gs,1,w,v,2,v,2,0,0,left,out)==1
        assert list(out)==[77]*24
        report=dict(status='PASS',complete_layer_cases=cases,rounds=rounds,independent_polynomial_evaluations=3*rounds,
            wrapper_rejections=len(bad_calls),direct_abi_rejections=3,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            scope='Native Ext8 GKR round coefficients and folds over complete two-axis synthetic layers, all add/sub/mul operations. No Fiat-Shamir transcript, full circuit/PCS proof, Rust refinement or security claim.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
