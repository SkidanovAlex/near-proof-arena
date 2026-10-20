"""Actual full-height proof binding regressions; not a soundness estimate."""
import copy,json,sys,hashlib
from pathlib import Path
from pq384_batched_codec import decode,encode
from pq384_batched_fold import verify,P
root=Path(sys.argv[1]);wire=(root/'proof.bin').read_bytes()
args=json.loads((root/'statement.json').read_text())
for k in ('statement','parent_binding','expected_root'):args[k]=bytes.fromhex(args[k])
shape=[args[k] for k in ('log_rows','width','packing')]
proof=decode(wire,*shape);assert verify(proof,**args)
rejected=[]
def reject(label,p,a):
    try:verify(p,**a)
    except ValueError as e:rejected.append({'case':label,'reason':str(e)})
    else:raise AssertionError('mutation accepted: '+label)
def bump(v):return (v+1)%P
def hexflip(h):return bytes([bytes.fromhex(h)[0]^1]).hex()+h[2:]
for key in ('statement','parent_binding','expected_root'):
    a=copy.deepcopy(args);v=a[key];a[key]=bytes([v[0]^1])+v[1:];reject(key,proof,a)
for j in (0,271,543):
    a=copy.deepcopy(args);a['column_claims'][j][0]=bump(a['column_claims'][j][0]);reject('column '+str(j),proof,a)
for j in (0,6,12):
    a=copy.deepcopy(args);a['row_point'][j][3]=bump(a['row_point'][j][3]);reject('point '+str(j),proof,a)
for ri in range(len(proof['rounds'])):
    for kind in ('quadratic','root','source_leaf','source_path','next_leaf','next_path','query_order'):
        p=copy.deepcopy(proof);rd=p['rounds'][ri]
        if kind=='quadratic':rd['quadratic'][0][0]=bump(rd['quadratic'][0][0])
        elif kind=='root':rd['next_root']=hexflip(rd['next_root'])
        elif kind=='query_order':rd['queries'][0],rd['queries'][-1]=rd['queries'][-1],rd['queries'][0]
        else:
            side,part=kind.split('_');q=rd['queries'][0][side]
            if part=='leaf':q['leaf'][0]=bump(q['leaf'][0])
            else:q['path'][0]=hexflip(q['path'][0])
        # Ensure mutations survive canonical serialization before checking semantics.
        reject(f'round{ri}/{kind}',decode(encode(p,*shape),*shape),args)
for i in (0,31,63):
    p=copy.deepcopy(proof);v=p['terminal']['coefficients'][0][i];v[2]=bump(v[2]);reject('terminal'+str(i),p,args)
p=copy.deepcopy(proof);p['rounds'].pop();reject('missing round',p,args)
p=copy.deepcopy(proof);p['rounds'].append(copy.deepcopy(p['rounds'][-1]));reject('extra round',p,args)
report={'status':'PASS','proof_sha256':hashlib.sha256(wire).hexdigest(),'negative_checks':len(rejected),'cases':rejected,'scope':'Fixed actual full-height proof mutation tests, not adaptive forgery soundness or security certification'}
(root/'binding-regressions.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS:',len(rejected),'full-height binding rejections')
