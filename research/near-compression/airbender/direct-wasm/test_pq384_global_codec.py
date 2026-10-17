"""Lossless shared-path codec, authenticated mutations and size accounting."""
import argparse,json,struct,sys
from array import array
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--library',required=True)
    ap.add_argument('--full-proof',required=True);ap.add_argument('--full-statement',required=True);ap.add_argument('--output-dir',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_global_codec as codec
    import pq384_global_chain as gc
    import pq384_batched_fold as old
    from pq384_native_fft import NativeFFT
    from packed_claim_handoff import packing_context,mle_ext
    from pq384_one_fold import base
    native=NativeFFT(a.library);rows=[[i+j+1 for j in range(19)] for i in range(8)]
    matrices=[];degree=128
    for lane in range(2):
        cs=[rows[i][lane*16+j] if lane*16+j<19 else 0 for j in range(16) for i in range(8)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:cs[i]=(cs[i]-cs[i^bit])%gc.P
            bit*=2
        matrices.append([base(v) for v in cs])
    ctx=packing_context(3,19,16);root,layers,leaves=old.source_tree(matrices,ctx)
    class Cache:
        def coefficients(self,lane):return array('I',(v[0] for v in matrices[lane]))
        def opening(self,i):return old.opening(layers,leaves,i)
    cache=Cache();cache.root=root;cache.context=ctx;cache.degree=degree;cache.lanes=2
    point=[(2,3,5,7),(11,13,17,19),(23,29,31,37)]
    args=dict(statement=b'globalcodec',parent_binding=b'fixedparent',expected_root=root,
              log_rows=3,width=19,packing=16,row_point=point,
              column_claims=[mle_ext([base(row[j]) for row in rows],point) for j in range(19)])
    cases=[(gc.prove_cached(cache,native,terminal_degree=t,**args),args,t,'small'+str(t)) for t in (1,64)]
    fullargs=json.loads(Path(a.full_statement).read_text())
    for k in ('statement','parent_binding','expected_root'):fullargs[k]=bytes.fromhex(fullargs[k])
    cases.append((json.loads(Path(a.full_proof).read_text()),fullargs,1,'full'))
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True);reports=[];rejected=0
    for proof,args,terminal,name in cases:
        encoded=codec.encode(proof,terminal_degree=terminal,**args)
        assert codec.decode(encoded,terminal_degree=terminal,**args)==proof
        (out/(name+'.bin')).write_bytes(encoded)
        stages=codec.header(args,terminal,proof['rounds'],proof['terminal'])
        count,fixed,maximum=codec.limits(args,terminal)
        leaf_bytes=sum(len(set(indices))*4*words for _,_,_,indices,words in stages)
        sibling_bytes=sum(len(codec.mp.boundary(n,indices))*48 for _,_,n,indices,_ in stages)
        assert len(encoded)==fixed+leaf_bytes+sibling_bytes
        def reject(data,arguments=args,term=terminal):
            nonlocal rejected
            try:codec.decode(data,terminal_degree=term,**arguments)
            except (ValueError,TypeError,KeyError,IndexError):rejected+=1
            else:raise AssertionError('malformed/semantic input accepted')
        for data in (b'',encoded[:-1],encoded+b'\0',bytes(maximum+1),b'X'+encoded[1:]):reject(data)
        offsets=[len(codec.MAGIC),len(codec.MAGIC)+48,fixed-16,fixed,len(encoded)//2,len(encoded)-1]
        for pos in offsets:
            data=bytearray(encoded);data[pos]^=1;reject(bytes(data))
        data=bytearray(encoded);data[len(codec.MAGIC):len(codec.MAGIC)+4]=struct.pack('<I',gc.P);reject(bytes(data))
        data=bytearray(encoded);data[fixed:fixed+4]=struct.pack('<I',gc.P);reject(bytes(data))
        changed=dict(args);changed['parent_binding']=b'wrong-parent';reject(encoded,changed)
        changed=dict(args);changed['expected_root']=bytes([args['expected_root'][0]^1])+args['expected_root'][1:];reject(encoded,changed)
        reject(encoded,args,65-terminal)
        reports.append(dict(case=name,terminal_degree=terminal,rounds=count,bytes=len(encoded),
                            header_and_terminal_bytes=fixed,unique_leaf_bytes=leaf_bytes,
                            shared_sibling_bytes=sibling_bytes,individual_path_upper_bytes=maximum))
    report=dict(status='PASS',lossless_roundtrips=len(cases),negative_checks=rejected,cases=reports,
                scope='Unchanged diagnostic Q8 globalchain profile; codec adds no security theorem')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
