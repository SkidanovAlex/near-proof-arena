from prepared_memory_sender import table
def expr(e):
    op=e[0]
    if op=='trans':return '.isTransition'
    if op=='c':return f'(.const {e[1]})'
    if op=='v':return f'(.col {e[1]} {str(bool(e[2])).lower()})'
    if op=='+':return f'(.add {expr(e[1])} {expr(e[2])})'
    if op=='*':return f'(.mul {expr(e[1])} {expr(e[2])})'
    if op=='-':return f'(.neg {expr(e[1])})'
    raise ValueError(e)
from pathlib import Path
import sys
t=table();out=['import ZkFormal.Air.Basic','namespace NearCompression','open ZkFormal.Air']
for i,e in enumerate(t['constraints']):out.append(f'def preparedMemorySenderLiteral{i:04d} : Expr := {expr(e)}')
out.append('def preparedMemorySenderLiteralConstraints : List Expr := ['+',\n'.join(f'preparedMemorySenderLiteral{i:04d}' for i in range(len(t['constraints'])))+']')
for i,x in enumerate(t['interactions']):out.append(f'def preparedMemorySenderLiteralMessage{i} : List Expr := ['+',\n'.join(map(expr,x['msg']))+']')
out.append('def preparedMemorySenderLiteralTable : Table := ⟨795,preparedMemorySenderLiteralConstraints, ['+',\n'.join(f'{{bus := {x["bus"]},send := {str(x["send"]).lower()},mult := [.const 1],msg := preparedMemorySenderLiteralMessage{i}}}' for i,x in enumerate(t['interactions']))+'],22⟩')
out.append('end NearCompression')
Path(sys.argv[1]).write_text('\n'.join(out)+'\n')
