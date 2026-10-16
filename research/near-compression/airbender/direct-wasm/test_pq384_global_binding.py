"""Full-height saved global-chain proof regressions; not a security estimate."""
import copy,json,sys,hashlib
from pathlib import Path
from pq384_global_chain import verify,P
root=Path(sys.argv[1]);proof=json.loads((root/'proof.json').read_text());args=json.loads((root/'statement.json').read_text())
for k in ('statement','parent_binding','expected_root'):args[k]=bytes.fromhex(args[k])
assert verify(proof,terminal_degree=1,**args)
rejections=[]
def reject(label,p=proof,a=args,terminal=1):
    try:verify(p,terminal_degree=terminal,**a)
    except ValueError as e:rejections.append({'case':label,'reason':str(e)})
    else:raise AssertionError('accepted '+label)
def bump(v):return (v+1)%P
def flip(h):return bytes([bytes.fromhex(h)[0]^1]).hex()+h[2:]
for key in ('statement','parent_binding','expected_root'):
    a=copy.deepcopy(args);v=a[key];a[key]=bytes([v[0]^1])+v[1:];reject(key,a=a)
for col in (0,271,543):
    a=copy.deepcopy(args);a['column_claims'][col][0]=bump(a['column_claims'][col][0]);reject('claim'+str(col),a=a)
for j in (0,6,12):
    a=copy.deepcopy(args);a['row_point'][j][3]=bump(a['row_point'][j][3]);reject('point'+str(j),a=a)
for ri in range(len(proof['rounds'])):
    for kind in ('quadratic','root','source_leaf','source_path','next_leaf','next_path'):
        p=copy.deepcopy(proof);rd=p['rounds'][ri]
        if kind=='quadratic':rd['quadratic'][0][0]=bump(rd['quadratic'][0][0])
        elif kind=='root':rd['next_root']=flip(rd['next_root'])
        else:
            side,part=kind.split('_');q=p['queries'][0][ri][side]
            if part=='leaf':q['leaf'][0]=bump(q['leaf'][0])
            else:q['path'][0]=flip(q['path'][0])
        reject(f'stage{ri}/{kind}',p)
p=copy.deepcopy(proof);p['terminal']['coefficients'][0][0][2]=bump(p['terminal']['coefficients'][0][0][2]);reject('terminal',p)
p=copy.deepcopy(proof);p['queries'][0],p['queries'][-1]=p['queries'][-1],p['queries'][0];reject('chain order',p)
p=copy.deepcopy(proof);p['queries'][0][0],p['queries'][0][1]=p['queries'][0][1],p['queries'][0][0];reject('stage order',p)
p=copy.deepcopy(proof);p['queries'].pop();reject('missing chain',p)
p=copy.deepcopy(proof);p['queries'][0].pop();reject('missing stage',p)
p=copy.deepcopy(proof);p['rounds'].pop();reject('missing commitment',p)
reject('wrong externally selected terminal profile',terminal=64)
report=dict(status='PASS',proof_sha256=hashlib.sha256((root/'proof.json').read_bytes()).hexdigest(),negative_checks=len(rejections),cases=rejections,
    scope='Fixed full-height proof mutation tests only; no adaptive forgery bound')
(root/'binding-regressions.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS:',len(rejections),'global-chain binding rejections')
