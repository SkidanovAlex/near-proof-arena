"""Lossless binary opening codec and semantic verification regressions."""
import copy,json,sys
from pathlib import Path
from pq384_batched_codec import encode,decode,MAGIC,P
from pq384_batched_fold import verify

root=Path(sys.argv[1]);results=[]
for shape in ('64x17','64x68','8x544'):
    proof=json.loads((root/f'proof-{shape}.json').read_text())
    args=json.loads((root/f'statement-{shape}.json').read_text())
    for key in ('statement','parent_binding','expected_root'):args[key]=bytes.fromhex(args[key])
    dims=[args[k] for k in ('log_rows','width','packing')]
    wire=encode(proof,*dims);restored=decode(wire,*dims)
    assert restored==proof and verify(restored,**args)
    rejected=0
    cuts=sorted(set([0,1,len(MAGIC)-1,len(MAGIC),len(MAGIC)+47,len(MAGIC)+95,
                     len(wire)-1025,len(wire)-1024,len(wire)-1]
                    +[len(wire)*i//32 for i in range(1,32)]))
    invalid=[wire[:n] for n in cuts]+[wire+b'\x00',b'X'+wire[1:]]
    invalid.append(wire[:len(MAGIC)]+P.to_bytes(4,'little')+wire[len(MAGIC)+4:])
    for bad in invalid:
        try:decode(bad,*dims)
        except ValueError:rejected+=1
        else:raise AssertionError('malformed encoding accepted')
    bad=copy.deepcopy(proof);bad['terminal']['coefficients'][0][0][0]=(bad['terminal']['coefficients'][0][0][0]+1)%P
    restored_bad=decode(encode(bad,*dims),*dims)
    try:verify(restored_bad,**args)
    except ValueError:pass
    else:raise AssertionError('semantically changed proof accepted')
    (root/f'proof-{shape}.npbf').write_bytes(wire)
    results.append({'shape':shape,'binary_bytes':len(wire),
                    'compact_json_bytes':len(json.dumps(proof,separators=(',',':')).encode()),
                    'malformed_rejections':rejected,'semantic_mutation_rejected':True})
report={'status':'PASS','cases':results,
        'scope':'Complete standalone opening serialization; statement/claims supplied externally as in JSON verifier',
        'limits':['Not fullNEAR/AIRproof size','Diagnostic security parameters unchanged']}
(root/'codec-verified.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
