"""Emit closed Lean AIR values with shared expression DAGs; no trusted proofs."""
import json
from pathlib import Path
import prepared_code_table_air as lit
ROOT=Path(__file__).resolve().parents[2]
source=ROOT/'results/native-literal-byte-packed-input'
old,_=lit.make(json.loads((source/'fixture.json').read_text()))
new=json.loads((source/'spec.json').read_text())
lines=['import NearCompression.PreparedLiteral','import NearCompression.PackedHoldsRefinement','',
       'set_option maxRecDepth 65536','set_option maxHeartbeats 4000000',
       'namespace NearCompression','open ZkFormal.Air ZkFormal.V2','']
seen={}
def expr(e):
    key=json.dumps(e)
    if key in seen:return seen[key]
    tag=e[0]
    if tag=='c':rhs=f'.const {e[1]}'
    elif tag=='v':rhs=f'.col {e[1]} '+('true' if e[2] else 'false')
    elif tag=='p':rhs=f'.pub {e[1]}'
    elif tag in ['first','last','trans']:rhs={'first':'.isFirst','last':'.isLast','trans':'.isTransition'}[tag]
    elif tag in ['+','*']:rhs=('.add' if tag=='+' else '.mul')+' '+expr(e[1])+' '+expr(e[2])
    elif tag=='-':rhs='.neg '+expr(e[1])
    else:raise ValueError(tag)
    name=f'packedLiteralNode{len(seen):04d}';seen[key]=name
    lines.append(f'def {name} : Expr := {rhs}')
    return name

def list_expr(es):return '['+','.join(map(expr,es))+']'
def interaction(i):
    return '{bus:='+str(i['bus'])+',send:='+str(i['send']).lower()+',msg:='+list_expr(i['msg'])+',mult:='+list_expr(i['mult'])+'}'
for prefix,spec in [('packedOriginal',old),('packedCandidate',new)]:
    tables=[]
    for ti,t in enumerate(spec['air']['tables']):
        cs=list_expr(t['constraints']);inter='['+','.join(map(interaction,t['interactions']))+']'
        lines.append(f'def {prefix}Constraints{ti} : List Expr := {cs}')
        lines.append(f'def {prefix}Interactions{ti} : List Interaction := {inter}')
        name=f'{prefix}Table{ti}';tables.append(name)
        lines.append(f'def {name} : Table := {{width:={t["width"]},maxLog:={t["maxLog"]},constraints:={prefix}Constraints{ti},interactions:={prefix}Interactions{ti}}}')
    segs=[]
    for seg in spec['air']['pubSegs']:
        assert seg['prefix']==[] and seg['indexBase'] is None and seg['startAt'] is None
        segs.append('{'+','.join(f'{k}:={str(seg[k]).lower()}' for k in ['bus','send','width','countAt','start'])+'}')
    lines.append(f'def {prefix}Air : AirP := {{tables:=['+','.join(tables)+'],numBuses:='+str(spec['air']['numBuses'])+',numPub:='+str(spec['air']['numPub'])+',maxPub:='+str(spec['air']['maxPub'])+',pubSegs:=['+','.join(segs)+']}')
lines+=['','theorem packed_original_literal_eq : packedOriginalAir=preparedLiteralAir 193 := by rfl',
        '','end NearCompression']
path=ROOT/'NearCompression/PackedLiteralData.lean';path.write_text('\n'.join(lines)+'\n')
print(f'Wrote {path.name}: {len(seen)} shared expression nodes, {path.stat().st_size} bytes')
# Individual kernel witnesses keep each rewrite reduction independently checkable.
from packed_byte_air import column_layout
from prepared_function_air import c,v,sub,mul
regions=[[(lit.STACK,256),(lit.GAS,64),(lit.DIFF,64),(lit.RESULT,32),(lit.IMM,32),(lit.FEE,64)],[(lit.CIMM,32),(lit.CFEE,64)]]
coverage=['import NearCompression.PackedLiteralData','set_option maxRecDepth 65536','set_option maxHeartbeats 16000000',
    'namespace NearCompression','open ZkFormal.Air',
    'private theorem coverageCons (P : Expr → Prop) (e : Expr) (es : List Expr)',
    '    (head : P e) (tail : ∀ x∈es,P x) : ∀ x∈e::es,P x := by',
    '  intro x hx; rcases List.mem_cons.mp hx with h | h',
    '  · exact h ▸ head','  · exact tail x h','']
for ti,(table,groups) in enumerate(zip(old['air']['tables'],regions)):
    removed,mapping,bytecols,_=column_layout(table['width'],groups)
    bits={oldcol+bit:(newcol,bit) for oldcol,newcol in bytecols.items() for bit in range(8)}
    skip={json.dumps(sub(mul(v(i),sub(v(i),c(1))),c(0))):('boolean',i) for i in removed}
    if ti==1:skip.update({json.dumps(mul(sub(c(1),v(0)),sub(v(i),c(0)))):('inactive',i) for i in removed})
    region='packedExecRegions' if ti==0 else 'packedCodeRegions'
    target=f'packedCandidateConstraints{ti}';cursor=0;names=[]
    for ci,e in enumerate(table['constraints']):
        name=f'packedCoverage{ti}_{ci:04d}';names.append(name)
        src=seen[json.dumps(e)]
        coverage.append(f'theorem {name} : PackedConstraintWitness {region} {target} {src} := by')
        dropped=skip.get(json.dumps(e))
        if dropped:
            kind,col=dropped;j,bit=bits[col]
            if kind=='boolean':coverage.append(f'  exact .boolean {col} {j} {bit} (by decide)')
            else:
                targetExpr=mul(sub(c(1),v(mapping[0])),v(j))
                idx=new['air']['tables'][ti]['constraints'].index(targetExpr)
                coverage.append(f'  exact .inactive 0 {mapping[0]} {col} {j} {bit} (by decide) (by decide) (List.mem_of_getElem (l:={target}) (i:={idx}) (h:=by decide) rfl)')
        else:
            dst=seen[json.dumps(new['air']['tables'][ti]['constraints'][cursor])]
            coverage.append(f'  exact .retained {src} {dst} (by decide +kernel) (List.mem_of_getElem (l:={target}) (i:={cursor}) (h:=by decide) rfl)')
            cursor+=1
    # One finite membership proof covers the complete original ordered list.
    proof='(by intro x hx; cases hx)'
    for name in reversed(names):proof=f'(coverageCons _ _ _ {name} {proof})'
    coverage.append(f'theorem packedCoverageTable{ti} : ∀ e∈packedOriginalConstraints{ti}, PackedConstraintWitness {region} {target} e :=\n  {proof}')
coverage+=['end NearCompression']
path=ROOT/'NearCompression/PackedLiteralCoverage.lean';path.write_text('\n'.join(coverage)+'\n')
print(f'Wrote {path.name}: {len(names)} constraints in last table, {path.stat().st_size} bytes')
