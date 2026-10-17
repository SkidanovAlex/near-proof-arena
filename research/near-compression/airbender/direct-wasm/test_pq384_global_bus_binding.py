"""Binding regressions for complete multi-table SHA384 diagnostic."""
import copy,json,sys
from pathlib import Path
from pq384_global_bus import verify,P
for directory in sys.argv[1:]:
    out=Path(directory);proof=json.loads((out/'proof.json').read_text());st=json.loads((out/'statement.json').read_text())
    spec=st['spec'];roots=[bytes.fromhex(v) for v in st['roots']];assert verify(proof,spec,roots)
    results=[]
    def reject(label,p=proof,s=spec,r=roots):
        try:verify(p,s,r)
        except ValueError as e:results.append(dict(case=label,reason=str(e)))
        else:raise AssertionError('accepted '+label)
    def flip(h):return bytes([bytes.fromhex(h)[0]^1]).hex()+h[2:]
    for ti in sorted(set([0,len(roots)//2,len(roots)-1])):
        rr=roots[:];rr[ti]=bytes([rr[ti][0]^1])+rr[ti][1:];reject('source root'+str(ti),r=rr)
        p=copy.deepcopy(proof);p['aux_roots'][ti]=flip(p['aux_roots'][ti]);reject('aux root'+str(ti),p)
        p=copy.deepcopy(proof);v=p['tables'][ti]['constraint_rounds'][0][0];v[0]=(v[0]+1)%P;reject('constraint'+str(ti),p)
        p=copy.deepcopy(proof);v=p['tables'][ti]['column_claims'][0];v[0]=(v[0]+1)%P;reject('claim'+str(ti),p)
        if proof['finals'][ti]:
            p=copy.deepcopy(proof);v=p['finals'][ti][0];v[0]=(v[0]+1)%P;reject('final'+str(ti),p)
        if len(proof['tables'][ti]['openings'])==2:
            p=copy.deepcopy(proof);p['tables'][ti]['openings'].reverse();reject('source aux branch swap'+str(ti),p)
    p=copy.deepcopy(proof);p['tables'].pop();reject('omitted table',p)
    p=copy.deepcopy(proof);p['tables'][0],p['tables'][-1]=p['tables'][-1],p['tables'][0];reject('table order',p)
    s=copy.deepcopy(spec);s['public'][0]=(s['public'][0]+1)%P;reject('public',s=s)
    s=copy.deepcopy(spec);s['terminal_degree']=64;reject('terminal profile',s=s)
    report=dict(status='PASS',tables=len(roots),negative_checks=len(results),cases=results,
       scope='Fixed proof/statement binding mutations; no adaptive security bound')
    (out/'binding-regressions.json').write_text(json.dumps(report,indent=2)+'\n');print(out.name,len(results),'PASS')
