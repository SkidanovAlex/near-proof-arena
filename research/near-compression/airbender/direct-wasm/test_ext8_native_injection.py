"""Native/reference parity, ABI rejection, full-size injection and FFT checks."""
import argparse,ctypes,json,random,subprocess,tempfile,time
from pathlib import Path
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel
import ext8_code_switch_functional as algebra
import ext8_code_switch_stage as stage


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(941276);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));cases=[];negative=[]
    with tempfile.TemporaryDirectory(prefix='native-injection-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True);native=Kernel(lib)
        for n in (1,2,8,128,1024):
            for q in (0,1,5):
                ws=[scalar() for _ in range(n)];claim=scalar();points=[scalar() if i%2==0 else f.base(rng.randrange(f.P)) for i in range(q)];answers=[scalar() for _ in points];mixers=[scalar() for _ in points]
                expected=algebra.inject(ws,claim,points,answers,mixers);assert native.inject(ws,claim,points,answers,mixers)==expected
                fn=native.inject_fn;native.inject_fn=None
                assert native.inject(ws,claim,points,answers,mixers)==expected;native.inject_fn=fn
                cases.append(dict(degree=n,constraints=q))
        def reject(name,fn):
            try:fn()
            except ValueError:negative.append(name)
            else:raise AssertionError(name)
        reject('empty-weights',lambda:native.inject([],f.ZERO,[],[],[]))
        reject('mixer-shape',lambda:native.inject([f.ONE],f.ZERO,[f.ONE],[f.ONE],[]))
        reject('noncanonical-weight',lambda:native.inject([[f.P]*8],f.ZERO,[],[],[]))
        reject('noncanonical-point',lambda:native.inject([f.ONE],f.ZERO,[[f.P]*8],[f.ONE],[f.ONE]))
        reject('constraint-cap',lambda:native.inject([f.ONE],f.ZERO,[f.ONE]*4097,[f.ONE]*4097,[f.ONE]*4097))
        # Direct ABI tests validate before output writes, including overlap.
        src=native.pack([f.ONE,f.ZERO]);terms=native.pack([f.ONE,f.ONE,f.ONE]);sentinel=1234567
        for name,n,q,cap,ss,tt,oo in [('abi-zero-degree',0,1,1,src,terms,None),('abi-capacity',1,1,1,src,terms,None),('abi-overlap',1,1,2,src,terms,src),('abi-null',1,1,2,None,terms,None),('abi-constraint-cap',1,4097,2,src,terms,None)]:
            out=(ctypes.c_uint32*16)(*[sentinel]*16) if oo is None else oo;before=list(out)
            assert native.inject_fn(ss,n,tt,q,out,cap)!=0 and list(out)==before;negative.append(name)
        bad=native.pack([f.ONE,f.ONE,f.ONE]);bad[0]=f.P;out=(ctypes.c_uint32*16)(*[sentinel]*16)
        assert native.inject_fn(src,1,bad,1,out,2)!=0 and list(out)==[sentinel]*16;negative.append('abi-noncanonical')
        n=131072;q=310;ws=[scalar() for _ in range(n)];claim=scalar();omega=pow(31,(f.P-1)//(8*n),f.P)
        unique=[scalar(),f.ONE,f.base(omega),f.base(omega*omega%f.P)];ans=[scalar() for _ in unique]
        labels=[0]+[1+i%3 for i in range(q-1)];points=[unique[i] for i in labels];answers=[ans[i] for i in labels];mixers=[scalar() for _ in labels]
        started=time.perf_counter();actual=native.inject(ws,claim,points,answers,mixers);native_seconds=time.perf_counter()-started
        # Independent reference reduces duplicate-point constraints algebraically.
        grouped=[f.ZERO]*4
        for index,mix in zip(labels,mixers):grouped[index]=f.add(grouped[index],mix)
        started=time.perf_counter();expected=algebra.inject(ws,claim,unique,ans,grouped);reference_seconds=time.perf_counter()-started
        assert actual==expected
        # Every value of a full1M FFT is checked against a sparse polynomial.
        N=1048576;cs=[f.ZERO]*N;cs[0]=scalar();cs[1]=scalar();cs[2]=scalar()
        started=time.perf_counter();values=native.fft(cs);fft_seconds=time.perf_counter()-started
        omega=pow(31,(f.P-1)//N,f.P);x=1
        for value in values:
            assert value==f.add(cs[0],f.add(f.scale(cs[1],x),f.scale(cs[2],x*x%f.P)));x=x*omega%f.P
        # Exact tree/root/leaf parity at non-LDE4 blowups.
        roots=[]
        for B in (2,8,16):
            coeff=[scalar() for _ in range(32)];namespace=stage.h.hash_parts(b'native-tree-parity').hex()
            ref=stage.tree(coeff,namespace,B,2);fast=stage.tree(coeff,namespace,B,2,native=native);assert fast==ref
            roots.append(dict(blowup=B,root=fast['root'].hex()))
        coeff=[scalar() for _ in range(32)];weights=[scalar() for _ in coeff];claim=algebra.dot(coeff,weights)
        namespace=stage.h.hash_parts(b'native-stage-parity').hex();root=stage.tree(coeff,namespace,4,2)['root'].hex()
        config=dict(profile=stage.PROFILE,degree=32,blowup=4,fold_bits=2,next_blowup=8,next_fold_bits=1,queries=8,namespace=namespace,parent=stage.h.hash_parts(b'parent').hex(),root=root)
        schedule=[dict(next_blowup=16,next_fold_bits=0,queries=8)]
        refproof=stage.prove_chain(coeff,config,weights,claim,schedule)
        fastproof=stage.prove_chain(coeff,config,weights,claim,schedule,native=native)
        assert fastproof==refproof
        assert stage.verify_chain(fastproof,config,weights,claim,schedule,native=native)
    result=dict(complete_chain_native_reference_identical=True,status='PASS',small_cases=cases,negative_cases=negative,large_injection=dict(degree=n,constraints=q,distinct_points=4,full_vector_parity=True,native_seconds=native_seconds,reference_grouped_seconds=reference_seconds),fft=dict(domain=N,all_values_sparse_polynomial_checked=True,seconds=fft_seconds),tree_parity=roots,scope='Arithmetic/native parity only. Duplicate-point large workload is not a random-query performance benchmark. No protocol soundness or full-slice size claim.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
