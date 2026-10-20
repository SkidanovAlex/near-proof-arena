"""Native local rounds versus direct multilinear/selector evaluation."""
import argparse, hashlib, json, random, subprocess, tempfile
from pathlib import Path
import pq384_ext8_reference as f
from pq384_ext8_local_native import NativeTable,library

def mle(rows,point,col):
    values=[f.base(row[col]) for row in rows]
    for r in point:values=f.affine_fold(values,r)
    return values[0]
def reference(rows,tau,point,c):
    first=last=eq=f.ONE
    for r,t in zip(point,tau):
        first=f.mul(first,f.sub(f.ONE,r));last=f.mul(last,r)
        eq=f.mul(eq,f.add(f.mul(r,t),f.mul(f.sub(f.ONE,r),f.sub(f.ONE,t))))
    x=mle(rows,point,0);y=mle(rows[1:]+rows[:1],point,1)
    result=f.mul(f.sub(f.add(f.mul(c,f.sub(x,y)),f.mul(first,x)),f.mul(last,y)),f.sub(f.ONE,last))
    return f.mul(eq,result)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rng=random.Random(88971)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    source=Path(__file__).with_name('native-folded')/'kernel_ext8_local.rs';checks=terminals=0;rejected=[]
    with tempfile.TemporaryDirectory(prefix='ext8-local-') as tmp:
        libpath=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(libpath)],check=True);lib=library(libpath)
        c=scalar();ins=[(0,0,0,*c)]+[(op,a,b,*f.ZERO) for op,a,b in [(1,0,0),(2,1,0),(3,0,0),(4,0,0),(5,0,0),(7,1,2),(8,6,0),(8,3,1),(6,7,8),(8,4,2),(7,9,10),(8,11,5)]]
        program=[x for row in ins for x in row]
        for n in (1,3,4):
            rows=[[rng.randrange(f.P) for _ in range(2)] for _ in range(1<<n)]
            for mode in ('zero','one','random'):
                tau=[scalar() for _ in range(n)];prefix=[]
                with NativeTable(rows,program,tau,lib) as state:
                    for bit in range(n):
                        actual=state.values(5)
                        for node,value in enumerate(actual):
                            expected=f.ZERO
                            for suffix in range(1<<(n-bit-1)):
                                point=prefix+[f.base(node)]+[f.base((suffix>>j)&1) for j in range(n-bit-1)]
                                expected=f.add(expected,reference(rows,tau,point,c))
                            assert value==expected;checks+=1
                        r=f.ZERO if mode=='zero' else f.ONE if mode=='one' else scalar()
                        state.fold(r);prefix.append(r)
                    cur,nxt=state.terminal()
                    assert cur==[mle(rows,prefix,j) for j in range(2)]
                    assert nxt==[mle(rows[1:]+rows[:1],prefix,j) for j in range(2)];terminals+=1
                    try:state.fold(f.ONE)
                    except ValueError:pass
                    else:raise AssertionError('extra fold accepted')
                try:state.terminal()
                except ValueError:pass
                else:raise AssertionError('closed state accepted')
        for name,offset,value in [('opcode',0,99),('cycle',12*11+1,12),('column',11+1,2),('constant',3,f.P)]:
            bad=list(program);bad[offset]=value
            with NativeTable([[0,1],[1,0]],bad,[f.ONE],lib) as state:
                try:state.values(5)
                except ValueError:rejected.append(name)
                else:raise AssertionError('bad program accepted')
        report=dict(status='PASS',round_node_comparisons=checks,terminal_pairs=terminals,malformed_programs=rejected,
            source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,source.with_name('kernel_ext8.rs'))},
            scope='Ext8 local instruction/selector/row-fold kernel, checked against direct full multilinear evaluation. No actual execution witness/local transcript or full slice proof yet; no Rust refinement/security certification.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
