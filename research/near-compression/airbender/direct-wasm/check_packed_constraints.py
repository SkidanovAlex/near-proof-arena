"""Check coverage certificates for every original constraint, plus negative cases."""
import copy,json,subprocess,tempfile
from pathlib import Path
import prepared_code_table_air as lit
from prepared_function_air import c,v,sub,mul
from packed_byte_air import column_layout
ROOT=Path(__file__).resolve().parents[2]
source=ROOT/'results/native-literal-byte-packed-input'
old,_=lit.make(json.loads((source/'fixture.json').read_text()))
packed=json.loads((source/'spec.json').read_text())
regions=[[(lit.STACK,256),(lit.GAS,64),(lit.DIFF,64),(lit.RESULT,32),(lit.IMM,32),(lit.FEE,64)],[(lit.CIMM,32),(lit.CFEE,64)]]
tasks=[];counts=[]
for ti,(before,after,groups) in enumerate(zip(old['air']['tables'],packed['air']['tables'],regions)):
    removed,_,_,_=column_layout(before['width'],groups)
    removed_exprs={json.dumps(sub(mul(v(i),sub(v(i),c(1))),c(0))):['boolean',i] for i in removed}
    if ti==1:removed_exprs.update({json.dumps(mul(sub(c(1),v(lit.CACTIVE)),sub(v(i),c(0)))):['inactive',lit.CACTIVE,i] for i in removed})
    entries=[];cursor=0;types={}
    for e in before['constraints']:
        cert=removed_exprs.get(json.dumps(e))
        if cert is None:cert=['retained',after['constraints'][cursor]];cursor+=1
        entries.append([e,cert]);types[cert[0]]=types.get(cert[0],0)+1
    tasks.append(dict(table=ti,target=after['constraints'],entries=entries));counts.append(types)
# Wrong scalar-as-byte, forged Boolean shape, missing target inactive constraint,
# and a retained certificate with an incorrect output must all fail.
negative=[dict(table=0,target=tasks[0]['target'],entries=[[sub(mul(v(0),sub(v(0),c(1))),c(0)),['boolean',0]]]),
    dict(table=0,target=tasks[0]['target'],entries=[[c(1),['boolean',lit.STACK]]]),
    dict(table=1,target=[],entries=[[mul(sub(c(1),v(0)),sub(v(lit.CIMM),c(0))),['inactive',0,lit.CIMM]]]),
    dict(table=0,target=tasks[0]['target'],entries=[[c(1),['retained',c(0)]]])]
with tempfile.TemporaryDirectory() as tmp:
    path=Path(tmp)/'certificates.json';path.write_text(json.dumps(tasks+negative))
    run=subprocess.run(['lake','env','lean','--run','PackedConstraintCheck.lean',str(path)],cwd=ROOT,text=True,capture_output=True,check=True)
answers=json.loads(run.stdout)
assert answers[:2]==[[True]*len(t['entries']) for t in tasks]
assert answers[2:]==[[False]]*len(negative)
print(json.dumps(dict(status='PASS',constraints=sum(len(t['entries']) for t in tasks),tables=counts,negative_certificates_rejected=len(negative),
    scope='Every original constraint has an accepted certificate under a kernel-proved checker soundness theorem. Executable artifact correspondence is not yet a closed kernel theorem for concrete AIR; global bus transfer remains open.'),indent=2))
