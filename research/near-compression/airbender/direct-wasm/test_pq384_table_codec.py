"""Actual saved table proofs: lossless encoding and semantic rejection checks."""
import copy,json,sys
from pathlib import Path
from pq384_table_codec import encode,decode,MAGIC,P
from pq384_table_air import verify_table_local
for directory in sys.argv[1:]:
    root=Path(directory);a=json.loads((root/'table-proof.json').read_text());spec=a['spec'];expected=bytes.fromhex(a['root'])
    wire=encode(a['proof'],spec);proof=decode(wire,spec)
    assert proof==a['proof'] and verify_table_local(proof,spec,expected)
    bad=[wire[:len(wire)*i//32] for i in range(32)]+[wire[:-1],wire+b'\0',b'X'+wire[1:],wire[:6]+P.to_bytes(4,'little')+wire[10:]]
    for b in bad:
        try:decode(b,spec)
        except ValueError:pass
        else:raise AssertionError('malformed accepted')
    semantic=0
    for section in ('constraint','current','next','claim','shift'):
        p=copy.deepcopy(proof)
        v={'constraint':p['constraint_rounds'][0][0],'current':p['shift_reduction']['current_evals'][0],
           'next':p['shift_reduction']['next_evals'][0],'claim':p['column_claims'][0],
           'shift':p['shift_reduction']['rounds'][0][0]}[section]
        v[0]=(v[0]+1)%P
        try:verify_table_local(decode(encode(p,spec),spec),spec,expected)
        except ValueError:semantic+=1
        else:raise AssertionError('semantic mutation accepted')
    (root/'proof.npta').write_bytes(wire)
    report=dict(status='PASS',binary_bytes=len(wire),malformed_rejections=len(bad),semantic_rejections=semantic,
        scope='Whole table-local proof payload; verifier-supplied spec/root external; not fullNEAR or secure profile')
    (root/'codec-verified.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
