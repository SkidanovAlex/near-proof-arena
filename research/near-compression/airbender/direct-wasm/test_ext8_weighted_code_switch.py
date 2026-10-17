"""Packed-root adapter tests with heterogeneous degrees and pooled weights."""
import argparse,copy,json,random,subprocess,sys,tempfile,time
from pathlib import Path
import ext8_weighted_code_switch as a
import pq384_ext8_reference as f
from pq384_ext8_native import Kernel
from test_ext8_input_weights import coefficient_claim
import ext8_pooled_weights as pool


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);args=p.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(930182);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));start=time.perf_counter();cases=[];pair_checks=0
    with tempfile.TemporaryDirectory(prefix='weighted-switch-') as temp:
        lib=Path(temp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True)
        native=Kernel(lib);caches=[];branches=[];claim=f.ZERO
        for n,width,packing in [(4,5,4),(2,3,2)]:
            rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<n)]
            cache=a.pcs.Source(rows,packing,native);caches.append(cache)
            branch=dict(root=cache.root.hex(),log_rows=n,width=width,packing=packing,row_point=[scalar() for _ in range(n)],
                lanes=[[[scalar() if j*packing+c<width else f.ZERO for c in range(packing)] for _ in range(2)] for j in range(cache.lanes)])
            branches.append(branch);claim=f.add(claim,coefficient_claim(rows,branch))
        for pooled in (False,True):
            if pooled:
                rows=[[rng.randrange(f.P) for _ in range(5)] for _ in range(8)]
                cache=a.pcs.Source(rows,2,native);caches.append(cache)
                terms=[dict(offset=off,width=w,row_point=[scalar() for _ in range(n)],current=[scalar() for _ in range(w)],next=[scalar() for _ in range(w)]) for off,w,n in [(0,3,3),(3,2,1)]]
                branches.append(dict(root=cache.root.hex(),log_rows=3,width=5,packing=2,terms=terms));claim=f.add(claim,pool.direct_claim(rows,terms))
            degrees=[c.degree for c in caches];D=max(degrees);betas=[[scalar() for _ in range(c.lanes)] for c in caches];combined=[f.ZERO]*D
            for c,bs in zip(caches,betas):
                for j,b in enumerate(bs):
                    for i,x in enumerate(c.coefficients(j)):combined[i*(D//c.degree)]=f.add(combined[i*(D//c.degree)],f.scale(b,x))
            omega=pow(440564289,(1<<27)//(4*D),f.P)
            for index in range(2*D):
                ops=[c.opening(index%(2*c.degree)) for c in caches]
                pair=a.source_pair(ops,index,branches,degrees,D,[c.context for c in caches],betas)
                x=f.base(pow(omega,index,f.P));assert pair==(f.evaluate(combined,x),f.evaluate(combined,f.sub(f.ZERO,x)));pair_checks+=1
            for queries in (8,31):
                config=dict(queries=queries,child_blowup=8,child_fold_bits=2,tail_steps=[dict(next_blowup=16,next_fold_bits=1,queries=queries),dict(next_blowup=8,next_fold_bits=0,queries=queries)])
                proof=a.prove(caches,native,b'statement',b'parent',branches,claim,config)
                assert a.verify(json.loads(json.dumps(proof)),b'statement',b'parent',branches,claim,config)
                cases.append(dict(pooled=pooled,queries=queries,degrees=degrees,terminal_coefficients=len(proof['terminal']),json_bytes=len(a.stage.canonical_json(proof))))
    statement=dict(statement=b'statement'.hex(),parent=b'parent'.hex(),branches=branches,claim=claim,config=config)
    (args.output/'proof.json').write_bytes(a.stage.canonical_json(proof));(args.output/'statement.json').write_bytes(a.stage.canonical_json(statement))
    fresh=subprocess.run([sys.executable,a.__file__,'--proof',str(args.output/'proof.json'),'--statement',str(args.output/'statement.json')],text=True,capture_output=True)
    (args.output/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode();negatives=[]
    def verify(p,st=statement):return a.verify(p,bytes.fromhex(st['statement']),bytes.fromhex(st['parent']),st['branches'],st['claim'],st['config'])
    def reject(name,p,st=statement):
        try:verify(p,st)
        except ValueError:negatives.append(name)
        else:raise AssertionError(name)
    def mutate(name,fn):
        p=copy.deepcopy(proof);fn(p);reject(name,p)
    def flip(v):v[0]=(v[0]+1)%f.P
    mutate('input-reduction',lambda p:flip(p['reduction'][0][0]))
    mutate('first-quadratic',lambda p:flip(p['first']['quadratic'][0]))
    mutate('first-child-root',lambda p:p['first'].__setitem__('child_root','ab'*48))
    mutate('first-ood',lambda p:flip(p['first']['ood_answer']))
    mutate('source-leaf',lambda p:flip(p['first']['source_openings'][0][1]['leaf']))
    mutate('source-path',lambda p:p['first']['source_openings'][0][0]['path'].__setitem__(0,'ab'*48))
    mutate('missing-source-branch',lambda p:p['first']['source_openings'][0].pop())
    mutate('missing-source-query',lambda p:p['first']['source_openings'].pop())
    mutate('source-order',lambda p:p['first']['source_openings'][0].reverse())
    mutate('untrusted-scalar-root',lambda p:p['first'].__setitem__('source_root','ab'*48))
    mutate('tail-quadratic',lambda p:flip(p['tail'][0]['rounds'][0][0]))
    mutate('tail-count',lambda p:p['tail'].pop())
    mutate('terminal',lambda p:flip(p['terminal'][0]))
    mutate('profile',lambda p:p.__setitem__('profile',a.pcs.PROFILE))
    mutate('noncanonical',lambda p:p['first']['ood_answer'].__setitem__(0,f.P))
    for name in ('source-root','source-weight','pooled-offset','claim','parent','schedule','queries'):
        st=copy.deepcopy(statement)
        if name=='source-root':st['branches'][1]['root']='ab'*48
        elif name=='source-weight':st['branches'][0]['lanes'][0][0][0]=list(f.ONE)
        elif name=='pooled-offset':st['branches'][-1]['terms'][1]['offset']=2
        elif name=='claim':st['claim']=list(f.add(claim,f.ONE))
        elif name=='parent':st['parent']=b'other-parent'.hex()
        elif name=='schedule':st['config']['tail_steps'][0]['next_blowup']=8
        else:st['config']['queries']=30
        reject('external-'+name,proof,st)
    report=dict(status='PASS',cases=cases,exhaustive_pair_checks=pair_checks,negative_cases=negatives,fresh_verifier=fresh.stdout.strip(),seconds=time.perf_counter()-start,
        scope='Original packed roots authenticated into scalar code-switch tail; small diagnostic fixtures, JSON encoding, no full execution bundle or proximity/extraction/QROM certificate.')
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
