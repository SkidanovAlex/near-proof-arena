"""Weighted Ext8 PCS diagnostic with heterogeneous source degrees."""
import argparse, copy, hashlib, json, random, subprocess, tempfile
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_weighted as p
import pq384_ext8_weighted_codec as codec
from pq384_ext8_native import Kernel
from test_ext8_input_weights import coefficient_claim

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();rng=random.Random(82273)
    def scalar():return tuple(rng.randrange(f.P) for _ in range(8))
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='ext8-weighted-') as tmp:
        path=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(path)],check=True);native=Kernel(path)
        caches=[];branches=[];claim=f.ZERO;data=[]
        for n,width,packing in ((2,3,2),(3,2,2)):
            rows=[[rng.randrange(f.P) for _ in range(width)] for _ in range(1<<n)];data.append(rows)
            cache=p.Source(rows,packing,native);caches.append(cache)
            lanes=[[[scalar() if j*packing+c<width else f.ZERO for c in range(packing)] for _ in range(2)] for j in range(cache.lanes)]
            branch=dict(root=cache.root.hex(),log_rows=n,width=width,packing=packing,row_point=[scalar() for _ in range(n)],lanes=lanes);branches.append(branch)
            claim=f.add(claim,coefficient_claim(rows,branch))
        results=[]
        for queries in (8,309):
            proof=p.prove(caches,native,b'statement',b'parent',branches,claim,queries=queries)
            wire=json.loads(json.dumps(proof));assert p.verify(wire,b'statement',b'parent',branches,claim,queries=queries)
            binary=codec.encode(wire,b'statement',b'parent',branches,claim,queries=queries)
            assert codec.decode(binary,b'statement',b'parent',branches,claim,queries=queries)==wire
            assert codec.verify(binary,b'statement',b'parent',branches,claim,queries=queries)
            shared=codec.encode(wire,b'statement',b'parent',branches,claim,queries=queries,shared_sources=True)
            assert shared[8:]==binary[8:]  # Distinct sources must not alias.
            assert codec.decode(shared,b'statement',b'parent',branches,claim,queries=queries)==wire
            assert codec.verify(shared,b'statement',b'parent',branches,claim,queries=queries)
            results.append(dict(binary_bytes=len(binary),queries=queries,rounds=len(proof['rounds']),json_bytes=len(json.dumps(wire,separators=(',',':')).encode())))
        # Mutations use the final309-query proof.
        mutations=[('reduction',lambda x:x['reduction'][0][0].__setitem__(0,(x['reduction'][0][0][0]+1)%f.P)),
            ('fold',lambda x:x['rounds'][0]['quadratic'][0].__setitem__(0,(x['rounds'][0]['quadratic'][0][0]+1)%f.P)),
            ('source-leaf',lambda x:x['queries'][0]['sources'][0]['leaf'].__setitem__(0,(x['queries'][0]['sources'][0]['leaf'][0]+1)%f.P)),
            ('path',lambda x:x['queries'][0]['sources'][0]['path'].__setitem__(0,'00'*48)),
            ('terminal',lambda x:x['terminal'].__setitem__(0,(x['terminal'][0]+1)%f.P)),
            ('query-count',lambda x:x['queries'].pop()),
            ('noncanonical',lambda x:x['rounds'][0]['quadratic'][0].__setitem__(0,f.P))]
        rejected=[]
        for name,mutate in mutations:
            bad=copy.deepcopy(wire);mutate(bad)
            try:p.verify(bad,b'statement',b'parent',branches,claim,queries=309)
            except ValueError:rejected.append(name)
            else:raise AssertionError('accepted '+name)
        bad_branch=copy.deepcopy(branches);bad_branch[0]['root']='00'*48
        bad_weights=copy.deepcopy(branches);bad_weights[0]['lanes'][0][0][0]=f.add(bad_weights[0]['lanes'][0][0][0],f.ONE)
        for name,st,pa,bs,cl,q in [('statement',b'changed',b'parent',branches,claim,309),('parent',b'statement',b'changed',branches,claim,309),
            ('root',b'statement',b'parent',bad_branch,claim,309),('weights',b'statement',b'parent',bad_weights,claim,309),
            ('claim',b'statement',b'parent',branches,f.add(claim,f.ONE),309),('query-budget',b'statement',b'parent',branches,claim,308)]:
            try:p.verify(wire,st,pa,bs,cl,queries=q)
            except ValueError:rejected.append(name)
            else:raise AssertionError('accepted '+name)
        assert [p.Source(rows,b['packing'],native).root.hex() for rows,b in zip(data,branches)]==[b['root'] for b in branches]
        # Independent reference FFT/root for every lane of the first source.
        cache=caches[0];ctx=cache.context;d=cache.degree;omega=pow(440564289,(1<<27)//(4*d),f.P)
        evals=[f.fft([f.base(c) for c in cs]+[f.ZERO]*(3*d),omega) for cs in cache.coeff]
        leaves=[p.h.field_words([v for lane in evals for v in (lane[i][0],lane[i+2*d][0])]) for i in range(2*d)]
        assert p.h.merkle_tree(leaves,ctx)[0]==cache.root
        report=dict(status='PASS',cases=results,rejections=rejected,source_root_reference_match=True,
            source_sha256=hashlib.sha256(Path(p.__file__).read_bytes()).hexdigest(),
            scope='Heterogeneous-degree weighted Ext8 folding diagnostic with opening-independent source commitments and externally supplied weights/claim. Query309 is a configuration test, not certified128-bit/PQ security. This test covers compact codec parity; complete secure envelope and formal implementation binding remain open.')
        args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
