"""Pooled weight-family PCS, mixed source degrees, and transcript binding."""
import argparse,copy,json,random,subprocess,tempfile
from pathlib import Path
from unittest.mock import patch
import pq384_ext8_reference as f
import pq384_ext8_weighted as p
import pq384_ext8_weighted_codec as codec
import pq384_ext8_weight_families as family
import ext8_pooled_weights as pool
from pq384_ext8_native import Kernel
from ext8_coefficient_claim_contract import coefficient_claim as legacy_claim


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    rng=random.Random(93201);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));results=[];rejected=[]
    def reject(name,action):
        try:action()
        except ValueError:rejected.append(name)
        else:raise AssertionError(name)
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='pooled-pcs-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True);native=Kernel(lib)
        rows=[[rng.randrange(f.P) for _ in range(7)] for _ in range(4)]
        cache=p.Source(rows,2,native)
        terms=[dict(offset=offset,width=width,row_point=[scalar() for _ in range(n)],current=[scalar() for _ in range(width)],next=[scalar() for _ in range(width)])
               for offset,width,n in ((1,2,2),(4,2,1),(2,2,1))]
        terms.append(dict(offset=6,width=1,row_point=[scalar()],current=[f.ZERO],next=[f.ZERO]))
        bank=dict(root=cache.root.hex(),log_rows=2,width=7,packing=2,terms=terms)
        claim=pool.direct_claim(rows,terms);assert pool.coefficient_claim(rows,terms,2)==claim
        for j in range(cache.lanes):
            expected=pool.lane_weights(terms,2,7,j*2,2)
            assert family.lane_weights(bank,j,native)==expected
            tensor=native.tensor;native.tensor=None
            assert family.lane_weights(bank,j,native)==expected;native.tensor=tensor
            point=[scalar() for _ in range(3)]
            from pq384_ext8_input_weights import mle
            assert mle(expected,point)==family.lane_beta(bank,j,point)
        other_rows=[[rng.randrange(f.P) for _ in range(2)] for _ in range(2)];other=p.Source(other_rows,1,native)
        old=dict(root=other.root.hex(),log_rows=1,width=2,packing=1,row_point=[scalar()],lanes=[[[scalar()],[scalar()]] for _ in range(2)])
        branches=[bank,old,copy.deepcopy(old)];caches=[cache,other,other]
        claim=f.add(claim,f.scale(legacy_claim(other_rows,old),2))
        for queries in (8,309):
            calls=[];implementation=family.lane_weights
            def counted(b,j,k):calls.append((b['root'],j));return implementation(b,j,k)
            with patch.object(family,'lane_weights',side_effect=counted):
                proof=p.prove(caches,native,b'pooled-test',b'parent',branches,claim,queries=queries)
            proof=json.loads(json.dumps(proof))
            assert proof['profile']==family.POOLED_PROFILE
            assert len(calls)==sum(p.lane_count(b) for b in branches)
            assert sum(root==bank['root'] for root,j in calls)==cache.lanes
            assert p.verify(proof,b'pooled-test',b'parent',branches,claim,queries=queries)
            sizes=[]
            for options in ({},{'shared_sources':True},{'derived_folds':True}):
                wire=codec.encode(proof,b'pooled-test',b'parent',branches,claim,queries=queries,**options)
                assert codec.decode(wire,b'pooled-test',b'parent',branches,claim,queries=queries)==proof
                assert codec.verify(wire,b'pooled-test',b'parent',branches,claim,queries=queries)
                sizes.append(len(wire))
            results.append(dict(queries=queries,bytes_full_shared_derived=sizes,total_weight_vectors=len(calls),pooled_weight_vectors=cache.lanes,logical_terms=len(terms)))
        def altered(name,mutate):
            bad=copy.deepcopy(branches);mutate(bad)
            reject(name,lambda:codec.verify(wire,b'pooled-test',b'parent',bad,claim,queries=309))
        altered('logical-offset',lambda b:b[0]['terms'][0].update(offset=2))
        altered('logical-height',lambda b:b[0]['terms'][1]['row_point'].append(list(f.ZERO)))
        altered('logical-weight',lambda b:b[0]['terms'][0]['current'].__setitem__(0,list(f.ONE)))
        altered('logical-order',lambda b:b[0]['terms'].reverse())
        altered('source-root',lambda b:b[0].update(root='00'*48))
        altered('empty-terms',lambda b:b[0].update(terms=[]))
        altered('wrong-schema',lambda b:b[0].update(row_point=[]))
        altered('out-of-bank',lambda b:b[0]['terms'][0].update(offset=7))
        bad=copy.deepcopy(proof);bad['profile']=p.PROFILE
        reject('legacy-profile',lambda:p.verify(bad,b'pooled-test',b'parent',branches,claim,queries=309))
        reject('changed-claim',lambda:codec.verify(wire,b'pooled-test',b'parent',branches,f.add(claim,f.ONE),queries=309))
        reject('query-budget',lambda:codec.verify(wire,b'pooled-test',b'parent',branches,claim,queries=308))
        reject('trailing',lambda:codec.verify(wire+b'\0',b'pooled-test',b'parent',branches,claim,queries=309))
        reject('authentication',lambda:codec.verify(wire[:-1]+bytes([wire[-1]^1]),b'pooled-test',b'parent',branches,claim,queries=309))
        # New generic tensor entry point must reject malformed shapes/canonicality.
        for name,args in [('tensor-empty',([],[],[f.ONE],[f.ONE])),('tensor-row-shape',([f.ONE],[f.ONE],[f.ONE],[])),
                          ('tensor-noncanonical',([f.ONE],[f.ONE],[(f.P,0,0,0,0,0,0,0)],[f.ONE]))]:
            reject(name,lambda args=args:native.tensor_weights(*args))
    report=dict(status='PASS',cases=results,rejections=rejected,native_and_reference_pooled_weights=True,
                scope='Pooled and legacy bank descriptors in one PCS, with one state vector per physical lane. Execution-to-bank root/phase mapping and PQ soundness remain unproved/unintegrated.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
