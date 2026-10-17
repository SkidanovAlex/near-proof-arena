import sys,json,collections,time
from pathlib import Path
from compile_swirl_gkr_verifier import compile_verifier,context
layout,slots,known,*_=context()
records=[]
for kind in ['output_first','inputs_first']+[f'interleaved_{p}{s}' for p in ['012','021','102','120','201','210'] for s in ['', '_high']]:
 t=time.monotonic();c,checks,residual,pcs=compile_verifier(layout,slots,set(known),kind)
 live=set(checks+[residual]+[w for _,w in pcs]);todo=list(live)
 while todo:
  node=c.nodes[todo.pop()]
  if node[0] not in ('const','input'):
   for i in node[1:]:
    if i not in live:live.add(i);todo.append(i)
 record=dict(kind=kind,nodes=len(c.nodes),live=len(live),ops=dict(collections.Counter(c.nodes[i][0] for i in live)),seconds=time.monotonic()-t)
 records.append(record);print(json.dumps(record),flush=True)

out=Path(__file__).resolve().parents[2]/'results/swirl-security-review/bdd-gkr-verifier'
out.mkdir(exist_ok=True)
(out/'orders.json').write_text(json.dumps(records,indent=2)+'\n')
