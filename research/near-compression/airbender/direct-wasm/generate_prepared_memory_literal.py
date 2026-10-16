"""Emit exact frozen scalar-memory-access-v1 table for Lean source extraction."""
from prepared_memory_air import table
from pathlib import Path
import sys
def expr(e):
    op=e[0]
    if op=='c':return f'(.const {e[1]})'
    if op=='v':return f'(.col {e[1]} {str(bool(e[2])).lower()})'
    if op=='+':return f'(.add {expr(e[1])} {expr(e[2])})'
    if op=='*':return f'(.mul {expr(e[1])} {expr(e[2])})'
    if op=='-':return f'(.neg {expr(e[1])})'
    raise ValueError(e)
def main(path):
    t=table();out=['import ZkFormal.Air.Basic','namespace NearCompression','open ZkFormal.Air']
    for i,e in enumerate(t['constraints']):out.append(f'def preparedMemoryLiteral{i:04d} : Expr := {expr(e)}')
    out.append('def preparedMemoryLiteralConstraints : List Expr := ['+',\n'.join(f'preparedMemoryLiteral{i:04d}' for i in range(len(t['constraints'])))+']')
    for i,x in enumerate(t['interactions']):
      out.append(f'def preparedMemoryLiteralMessage{i} : List Expr := ['+',\n'.join(map(expr,x['msg']))+']')
    out.append('def preparedMemoryLiteralTable : Table := ⟨460,preparedMemoryLiteralConstraints, [\n'+
      ',\n'.join(f'{{bus := {x["bus"]}, send := {str(x["send"]).lower()}, mult := [.const 1], msg := preparedMemoryLiteralMessage{i}}}' for i,x in enumerate(t['interactions']))+'],22⟩')
    out.append('end NearCompression')
    Path(path).write_text('\n'.join(out)+'\n')
if __name__=='__main__':main(sys.argv[1])
