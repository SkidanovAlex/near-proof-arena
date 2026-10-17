"""Exact old/new PCS proof parity, heterogeneous embeddings and tamper tests."""
import argparse,copy,hashlib,json,random,subprocess,tempfile
from pathlib import Path
import pq384_ext8_weighted_codec as c
import pq384_ext8_derived_codec as d
from pq384_ext8_native import Kernel
from ext8_coefficient_claim_contract import coefficient_claim
p,f=c.p,c.p.f


def check(proof,st,parent,branches,claim,queries):
    old=c.encode(proof,st,parent,branches,claim,queries=queries,shared_sources=True)
    wire=c.encode(proof,st,parent,branches,claim,queries=queries,derived_folds=True)
    assert c.decode(wire,st,parent,branches,claim,queries=queries)==proof
    assert c.verify(wire,st,parent,branches,claim,queries=queries)
    assert c.encode(c.decode(wire,st,parent,branches,claim,queries=queries),st,parent,branches,claim,queries=queries,derived_folds=True)==wire
    detail=d.breakdown(proof,st,parent,branches,claim,queries=queries)
    assert detail['total_bytes']==len(wire)
    assert len(old)-len(wire)==detail['derived_scalar_bytes_saved']
    return old,wire,detail


def main():
    a=argparse.ArgumentParser();a.add_argument('--capture',type=Path,required=True);a.add_argument('--output',type=Path,required=True);args=a.parse_args()
    proof=json.loads((args.capture/'proof.json').read_text());cfg=json.loads((args.capture/'opening.json').read_text())
    st,parent=bytes.fromhex(cfg['statement']),bytes.fromhex(cfg['parent']);branches,claim,queries=cfg['branches'],cfg['claim'],cfg['queries']
    old,wire,detail=check(proof,st,parent,branches,claim,queries)
    assert old==(args.capture/'proof.bin').read_bytes()
    (args.capture/'derived-proof.bin').write_bytes(wire)
    rejected=[]
    def reject(name,fn):
        try:fn()
        except ValueError:rejected.append(name)
        else:raise AssertionError('accepted '+name)
    cases=[('truncated',wire[:-1]),('trailing',wire+b'\0'),('version',b'BADMAGIC'+wire[8:]),
           ('old-format-relabel',c.SHARED_MAGIC+wire[8:]),('noncanonical-header',wire[:8]+f.P.to_bytes(4,'little')+wire[12:]),
           ('changed-source',wire[:detail['header_bytes']]+bytes([wire[detail['header_bytes']]^1])+wire[detail['header_bytes']+1:]),
           ('changed-authentication',wire[:-1]+bytes([wire[-1]^1]))]
    offset=detail['header_bytes']
    for stage in detail['stages']:
        if stage['kind']=='folds' and stage['leaf_bytes']:
            cases.append(('noncanonical-retained-fold',wire[:offset]+f.P.to_bytes(4,'little')+wire[offset+4:]));break
        offset+=stage['leaf_bytes']+stage['sibling_bytes']
    for name,bad in cases:
        reject(name,lambda bad=bad:c.verify(bad,st,parent,branches,claim,queries=queries))
    for name,s,pa,cl,q in [('statement',b'changed',parent,claim,queries),('parent',st,b'changed',claim,queries),
                          ('claim',st,parent,f.add(f.canonical(claim),f.ONE),queries),('query-budget',st,parent,claim,queries-1)]:
        reject(name,lambda s=s,pa=pa,cl=cl,q=q:c.verify(wire,s,pa,branches,cl,queries=q))
    bad=copy.deepcopy(branches);bad[0]['root']='00'*48
    reject('source-root',lambda:c.verify(wire,st,parent,bad,claim,queries=queries))
    bad=copy.deepcopy(branches);bad[0]['lanes'][0][0][0]=list(f.add(f.canonical(bad[0]['lanes'][0][0][0]),f.ONE))
    reject('weights',lambda:c.verify(wire,st,parent,bad,claim,queries=queries))
    # Two identical queried coordinates must never silently overwrite different values.
    reject('conflicting-derived-coordinate',lambda:d.derived_values(4,f.ZERO,[0,0],[(f.ZERO,f.ZERO),(f.ONE,f.ONE)]))
    rng=random.Random(92081);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));small=[]
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='ext8-derived-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True);native=Kernel(lib)
        for shapes in (((1,1,1),),((1,2,1),(2,3,2))):
            caches=[];bs=[];value=f.ZERO
            for n,width,packing in shapes:
                rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<n)];cache=p.Source(rows,packing,native)
                for repeat in range(2):
                    branch=dict(root=cache.root.hex(),log_rows=n,width=width,packing=packing,row_point=[scalar() for _ in range(n)],
                        lanes=[[[scalar() if j*packing+k<width else f.ZERO for k in range(packing)] for _ in range(2)] for j in range(cache.lanes)])
                    caches.append(cache);bs.append(branch);value=f.add(value,coefficient_claim(rows,branch))
            for q in (1,8,80):
                pr=json.loads(json.dumps(p.prove(caches,native,b'small',b'parent',bs,value,queries=q)))
                old_small,new_small,stats=check(pr,b'small',b'parent',bs,value,q)
                small.append(dict(degrees=[x.degree for x in caches],queries=q,old_bytes=len(old_small),new_bytes=len(new_small),
                                  derived_scalars=sum(x['derived_scalar_count'] for x in stats['stages'])))
    report=dict(status='PASS',old_bytes=len(old),new_bytes=len(wire),saved_bytes=len(old)-len(wire),breakdown=detail,
                decoded_proof_identical=True,negative_cases=rejected,small_cases=small,sha256=hashlib.sha256(wire).hexdigest(),
                scope='Same transcript, roots, queries and decoded PCS proof; transport-only reduction. No new proximity/QROM/PQ security claim.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
