"""Native Ext8 primitives versus independent Python arithmetic and round identity."""
import argparse, ctypes, hashlib, json, random, subprocess, tempfile, time
from pathlib import Path
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    rng=random.Random(804816)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    with tempfile.TemporaryDirectory(prefix='nearproof-ext8-kernel-') as tmp:
        lib=Path(tmp)/'kernel.so'
        subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True)
        k=Kernel(lib);basis=[tuple(int(i==j) for i in range(8)) for j in range(8)]
        for a in basis:
            for b in basis:assert k.affine_fold([f.ZERO,a],b)==[f.mul(a,b)]
        cases=0;identities=0;timings=[]
        for n in (0,2,4,16,256,4096):
            values=[scalar() for _ in range(n)];weights=[scalar() for _ in range(n)]
            if n==2:values=[(f.P-1,)*8]*2
            for r in (f.ZERO,f.ONE,scalar()):
                start=time.perf_counter();folded=k.affine_fold(values,r);q=k.quadratic(values,weights);native=time.perf_counter()-start
                start=time.perf_counter();assert folded==f.affine_fold(values,r);assert q==f.quadratic(values,weights);reference=time.perf_counter()-start
                folded_weights=f.affine_fold(weights,r);dot=f.ZERO
                for a,b in zip(folded,folded_weights):dot=f.add(dot,f.mul(a,b))
                assert f.evaluate(q,r)==dot
                original=f.ZERO
                for a,b in zip(values,weights):original=f.add(original,f.mul(a,b))
                assert f.add(q[0],f.evaluate(q,f.ONE))==original
                cases+=1;identities+=2
                if n==4096:timings.append(dict(native_seconds=native,reference_seconds=reference))
        rejected=0
        for action in (lambda:k.affine_fold([f.ZERO],f.ONE),lambda:k.quadratic([f.ZERO,f.ONE],[f.ZERO]),
                       lambda:k.affine_fold([f.ZERO,f.ONE],(f.P,)+(0,)*7),
                       lambda:k.quadratic([(0,)*7,f.ONE],[f.ZERO,f.ONE])):
            try:action()
            except ValueError:rejected+=1
            else:raise AssertionError('bad wrapper input accepted')
        # Direct ABI rejection is independent of Python validation. Check no writes.
        a=(ctypes.c_uint32*16)(*([0]*16));r=(ctypes.c_uint32*8)(*f.ONE)
        out=(ctypes.c_uint32*24)(*([123]*24));a[0]=f.P
        assert k.lib.near_ext8_fold(a,2,r,out)==1
        assert k.lib.near_ext8_quadratic(a,a,2,out)==1
        a[0]=0
        assert k.lib.near_ext8_fold(a,1,r,out)==1
        assert k.lib.near_ext8_quadratic(a,a,1,out)==1
        assert list(out)==[123]*24
        report=dict(status='PASS',basis_products=64,differential_cases=cases,round_identities=identities,
            wrapper_rejections=rejected,direct_abi_rejections=4,timings_4096=timings,
            source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            compiler=subprocess.run(['rustc','--version'],check=True,capture_output=True,text=True).stdout.strip(),
            scope='Native Ext8 fold/quadratic primitives only. Independent arithmetic and sumcheck identity tests; no Rust-to-Lean refinement, full native GKR/local prover, transcript, PCS integration, quantum security or proof-size claim.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
