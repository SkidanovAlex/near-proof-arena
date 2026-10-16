"""Ext8 native FFT/LDE4 vs Python, direct polynomial evaluation, and Merkle roots."""
import argparse, ctypes as C, hashlib, json, random, struct, subprocess, tempfile, time
from array import array
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_reusable as pcs
import pq384_primitives as h
from pq384_ext8_native import Kernel

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rng=random.Random(82197)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs';cases=evaluations=roots=0;timings=[]
    with tempfile.TemporaryDirectory(prefix='ext8-fft-') as tmp:
        path=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(path)],check=True);k=Kernel(path)
        for n in (1,2,8,64,4096):
            coeff=[scalar() for _ in range(n)]
            for lde in (False,True):
                domain=n*(4 if lde else 1);omega=pow(440564289,(1<<27)//domain,f.P)
                start=time.perf_counter();actual=k.fft(coeff,lde4=lde);native=time.perf_counter()-start
                start=time.perf_counter();expected=f.fft(coeff+[f.ZERO]*(domain-n),omega);python=time.perf_counter()-start
                assert actual==expected;cases+=1
                for i in sorted(set((0,domain//2,domain-1))):
                    assert actual[i]==f.evaluate(coeff,f.base(pow(omega,i,f.P)));evaluations+=1
                if n==4096:timings.append(dict(lde4=lde,domain=domain,native_seconds=native,python_seconds=python))
                if lde and n<=64:
                    context=h.hash_parts(b'ext8-native-fft-test',h.u64(n));half=domain//2
                    leaves=[pcs.extbytes(actual[i])+pcs.extbytes(actual[i+half]) for i in range(half)]
                    root,_=h.merkle_tree(leaves,context)
                    assert root==pcs.tree(coeff,context,False)['root'];roots+=1
        base=[f.base(rng.randrange(f.P)) for _ in range(64)]
        assert all(v[1:]==f.ZERO[1:] for v in k.fft(base,lde4=True))
        coeff=[rng.randrange(f.P) for _ in range(32)];point=[scalar() for _ in range(5)]
        claim=f.ZERO
        for c,weight in zip(coeff,pcs.eqweights(point)):claim=f.add(claim,f.scale(weight,c))
        cfg=dict(profile=pcs.PROFILE,degree=32,queries=8,point=point,claim=claim,statement=b'native-fft-test'.hex(),source_namespace=b'independent-source'.hex())
        root=pcs.source_tree(coeff,cfg)['root'];assert pcs.source_tree(coeff,cfg,kernel=k)['root']==root
        proof=pcs.prove(coeff,cfg,root,kernel=k);assert proof==pcs.prove(coeff,cfg,root)
        assert pcs.verify(proof,cfg,root)
        rejected=0
        for action in (lambda:k.fft([]),lambda:k.fft([f.ONE]*3),lambda:k.fft([(f.P,)+(0,)*7]),lambda:k.fft_words(array('I',[0]*7))):
            try:action()
            except ValueError:rejected+=1
            else:raise AssertionError('bad FFT input accepted')
        src=(C.c_uint32*16)(*([0]*16));out=(C.c_uint32*64)(*([99]*64))
        assert k.lib.near_ext8_fft(src,16,out,63,8)==1
        src[0]=f.P;assert k.lib.near_ext8_fft(src,16,out,64,8)==1;src[0]=0
        assert k.lib.near_ext8_fft(src,16,src,16,2)==1
        assert k.lib.near_ext8_fft(src,16,out,64,4)==1
        assert list(out)==[99]*64
        report=dict(reusable_pcs_native_reference_proof_identical=True,status='PASS',fft_cases=cases,direct_polynomial_evaluations=evaluations,merkle_root_comparisons=roots,
            base_source_preserved=True,wrapper_rejections=rejected,direct_abi_rejections=4,timings=timings,
            source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            scope='Native Ext8 FFT/LDE4 through degree4096/domain16384. Reference/root parity and direct evaluation checks; reusable scalar PCS proof parity; no weighted slice PCS integration, Rust refinement, quantum security or envelope-size certification.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
