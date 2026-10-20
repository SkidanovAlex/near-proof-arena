"""Run the proved concrete Lean rewriter over all actual source expressions.
Exact executable correspondence check; not a whole-AIR soundness theorem.
"""
import json,subprocess,tempfile
from pathlib import Path
import prepared_code_table_air as lit
from prepared_function_air import c,v,sub,mul
from packed_byte_air import transform,column_layout
ROOT=Path(__file__).resolve().parents[2]
source=ROOT/'results/native-literal-byte-packed-input'
old,rows=lit.make(json.loads((source/'fixture.json').read_text()))
packed,_,_=transform(old,rows)
assert packed==json.loads((source/'spec.json').read_text())
regions=[[(lit.STACK,256),(lit.GAS,64),(lit.DIFF,64),(lit.RESULT,32),(lit.IMM,32),(lit.FEE,64)],[(lit.CIMM,32),(lit.CFEE,64)]]
inputs=[];expected=[];counts=[]
for ti,(before,after,groups) in enumerate(zip(old['air']['tables'],packed['air']['tables'],regions)):
    removed,_,bytecols,_=column_layout(before['width'],groups)
    skip={json.dumps(sub(mul(v(i),sub(v(i),c(1))),c(0))) for i in removed}
    if ti==1:skip|={json.dumps(mul(sub(c(1),v(lit.CACTIVE)),sub(v(i),c(0)))) for i in removed}
    entries=list(before['constraints']);answers=[];cursor=0
    for expr in entries:
        if json.dumps(expr) in skip:answers.append(None)
        else:answers.append(after['constraints'][cursor]);cursor+=1
    assert cursor+(len(bytecols) if ti==1 else 0)==len(after['constraints'])
    rejected=sum(x is None for x in answers)
    interaction_exprs=0
    for old_i,new_i in zip(before['interactions'],after['interactions']):
        assert (old_i['bus'],old_i['send'])==(new_i['bus'],new_i['send'])
        for key in ('msg','mult'):
            assert len(old_i[key])==len(new_i[key])
            entries.extend(old_i[key]);answers.extend(new_i[key]);interaction_exprs+=len(old_i[key])
    assert len(after['interactions'])==len(before['interactions'])+len(bytecols)
    inputs.append(entries);expected.append(answers)
    counts.append(dict(source_constraints=len(before['constraints']),retained=cursor,removed=rejected,interaction_expressions=interaction_exprs))
with tempfile.TemporaryDirectory() as tmp:
    path=Path(tmp)/'expressions.json';path.write_text(json.dumps(inputs))
    run=subprocess.run(['lake','env','lean','--run','PackedRewriteCheck.lean',str(path)],cwd=ROOT,text=True,capture_output=True,check=True)
assert json.loads(run.stdout)==expected
print(json.dumps(dict(status='PASS',tables=counts,expression_count=sum(map(len,inputs)),
    scope='Every actual retained constraint/interaction AST equals the proved Lean rewrite. Rejected source expressions are exactly the intended removed constraints. Byte ranges, constraint assembly and global bus transfer remain open.'),indent=2))
