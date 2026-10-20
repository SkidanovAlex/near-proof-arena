"""Match theorem-backed Lean macro ASTs to every concrete Python rewrite pair."""
import json, subprocess, tempfile
from pathlib import Path
import prepared_code_table_air as lit
from packed_byte_air import macro_replacements
ROOT=Path(__file__).resolve().parents[2]
regions=[[(lit.STACK,256),(lit.GAS,64),(lit.DIFF,64),(lit.RESULT,32),(lit.IMM,32),(lit.FEE,64)],[(lit.CIMM,32),(lit.CFEE,64)]]
positions=[];expected=[]
for width,groups in zip([lit.WIDTH,lit.CWIDTH],regions):
    removed={i for start,n in groups for i in range(start,start+n)}
    starts={i for start,n in groups for i in range(start,start+n,8)}
    bytecols={};col=0
    for i in range(width):
        if i in starts:bytecols[i]=col;col+=1
        elif i not in removed:col+=1
    expected.extend([[json.loads(src),dst] for src,dst in macro_replacements(groups,bytecols).items()])
    for start,n in groups:
        for base in range(start,start+n,16):
            for nx in (False,True):
                lo,hi=bytecols[base],bytecols[base+8]
                positions.append([base,lo,hi,nx])
with tempfile.TemporaryDirectory() as d:
    source=Path(d)/'positions.json';source.write_text(json.dumps(positions))
    run=subprocess.run(['lake','env','lean','--run','PackedMacroExport.lean',str(source)],cwd=ROOT,text=True,capture_output=True,check=True)
actual=json.loads(run.stdout)
assert actual==expected
report=dict(status='PASS',macro_pairs=len(expected),current_rows=sum(not p[3] for p in positions),next_rows=sum(p[3] for p in positions),
    scope='Exact exported AST equality; universal field semantics kernel-proved in PackedByteMacro. Python execution/refinement and whole AIR implication remain unproved.')
print(json.dumps(report,indent=2))
