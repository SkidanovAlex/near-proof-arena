"""Differential tensor weights, malformed ABI, and representative timing."""
import argparse,ctypes as C,hashlib,json,random,subprocess,tempfile,time
from pathlib import Path
from pq384_ext8_native import Kernel
import pq384_ext8_reference as f
from pq384_ext8_input_weights import lane_weights


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(90322)
    scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory() as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True);k=Kernel(lib)
        cases=0
        for n in (0,1,3,7):
            for width in (1,2,8):
                point=[scalar() for _ in range(n)];u=[scalar() for _ in range(width)];v=[scalar() for _ in range(width)]
                assert k.lane_weights(point,u,v)==lane_weights(point,u,v);cases+=1
        point=[scalar() for _ in range(11)];u=[scalar() for _ in range(128)];v=[scalar() for _ in range(128)]
        start=time.perf_counter();ref=lane_weights(point,u,v);reference=time.perf_counter()-start
        start=time.perf_counter();actual=k.lane_weights(point,u,v);native=time.perf_counter()-start;assert actual==ref
        saved=k.tensor;k.tensor=None;assert k.lane_weights(point[:2],u[:2],v[:2])==lane_weights(point[:2],u[:2],v[:2]);k.tensor=saved
        buf=k.pack([f.ONE]);out=(C.c_uint32*8)();bad=k.pack([f.ONE]);bad[0]=f.P
        assert k.tensor(buf,buf,1,buf,buf,1,out,0)!=0
        assert k.tensor(bad,buf,1,buf,buf,1,out,1)!=0
        assert k.tensor(buf,buf,0,buf,buf,1,out,0)!=0
        rejects=[]
        for name,args in [('shape',([],[],[])),('width',([],[f.ONE]*3,[f.ONE]*3)),('canonical',([tuple([f.P]+[0]*7)],[f.ONE],[f.ONE]))]:
            try:k.lane_weights(*args)
            except ValueError:rejects.append(name)
            else:raise AssertionError(name)
        report=dict(status='PASS',small_cases=cases,representative_elements=len(ref),reference_seconds=reference,native_seconds=native,speedup=reference/native,old_library_fallback=True,abi_rejections=3,python_rejections=rejects,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),scope='Exact reference/native tensor parity, including representative2048x128 lane. Microbenchmark only, not end-to-end prover speedup or formal Rust refinement.')
        a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
