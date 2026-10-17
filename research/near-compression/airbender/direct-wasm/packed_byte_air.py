"""Byte-pack selected integer regions; fail closed on unhandled bit expressions.
New AIR requires a separate formal refinement; differential checks are not that proof.
"""
import copy,json
from collections import Counter
import prepared_code_table_air as lit
from prepared_function_air import c,v,sub,mul,sm,eval_expr

def macro_replacements(groups,bytecols):
    replacements={}
    for start,n in groups:
        for base in range(start,start+n,16):
            for nxt in (0,1):
                replacements[json.dumps(lit.bits(base,16,nxt))]=sm([v(bytecols[base],nxt),mul(c(256),v(bytecols[base+8],nxt))])
    return replacements

def transform(spec,rows):
    spec=copy.deepcopy(spec);packed=[];maps=[];all_counts=Counter();rewrites=[]
    regions=[[(lit.STACK,256),(lit.GAS,64),(lit.DIFF,64),(lit.RESULT,32),(lit.IMM,32),(lit.FEE,64)],[(lit.CIMM,32),(lit.CFEE,64)]]
    for ti,(table,trace,groups) in enumerate(zip(spec['air']['tables'],rows,regions)):
        removed={i for start,n in groups for i in range(start,start+n)}
        starts={i for start,n in groups for i in range(start,start+n,8)}
        mapping={};bytecols={};new_width=0
        for i in range(table['width']):
            if i in starts:bytecols[i]=new_width;new_width+=1
            elif i not in removed:mapping[i]=new_width;new_width+=1
        replacements=macro_replacements(groups,bytecols)
        def rewrite(e):
            key=json.dumps(e)
            if key in replacements:return replacements[key]
            if e[0]=='v':
                assert e[1] not in removed,('unhandled packed-bit use',ti,e)
                return v(mapping[e[1]],e[2])
            if e[0] in ('c','p','first','last','trans'):return e
            return [e[0]]+[rewrite(x) for x in e[1:]]
        skip={json.dumps(sub(mul(v(i),sub(v(i),c(1))),c(0))) for i in removed}
        # CODE inactive-row bit-zero obligations become byte-zero obligations.
        if ti==1:
            skip|={json.dumps(mul(sub(c(1),v(lit.CACTIVE)),sub(v(i),c(0)))) for i in removed}
        oldcs=table['constraints'];cs=[rewrite(e) for e in oldcs if json.dumps(e) not in skip]
        if ti==1:cs += [mul(sub(c(1),v(mapping[lit.CACTIVE])),v(j)) for j in bytecols.values()]
        for interaction in table['interactions']:
            interaction['msg']=[rewrite(e) for e in interaction['msg']]
            interaction['mult']=[rewrite(e) for e in interaction['mult']]
        table['interactions'] += [dict(bus=4,msg=[v(j)],mult=[c(1)],send=True) for j in bytecols.values()]
        table['constraints']=cs;table['width']=new_width
        output=[]
        for row in trace:
            nr=[0]*new_width
            for old,new in mapping.items():nr[new]=row[old]
            for old,new in bytecols.items():
                assert all(x in (0,1) for x in row[old:old+8])
                nr[new]=sum(row[old+i]<<i for i in range(8));all_counts[nr[new]]+=1
            output.append(nr)
        packed.append(output);maps.append(mapping)
        rewrites.append(dict(table=ti,packed_bit_columns=len(removed),byte_columns=len(bytecols),remaining_width=new_width,
            retained_source_constraints=len(oldcs)-sum(json.dumps(e) in skip for e in oldcs),range_interactions=len(bytecols)))
    # A receiver can only emit an 8-bit value; its 16-bit multiplicities bound
    # integer counts. Native LogUp must additionally enforce total-count limits.
    cs=[sub(mul(v(i),sub(v(i),c(1))),c(0)) for i in range(24)]
    range_table=dict(width=24,maxLog=22,constraints=cs,interactions=[dict(bus=4,msg=[lit.bits(0,8)],mult=[v(8+i) for i in range(16)],send=False)])
    table_rows=[]
    for value in range(256):
        count=all_counts[value];assert count<65536
        table_rows.append([(value>>i)&1 for i in range(8)]+[(count>>i)&1 for i in range(16)])
    spec['air']['tables'].append(range_table);spec['air']['numBuses']=5;spec['log_rows'].append(8);packed.append(table_rows)
    # Check every actual row constraint and the exact integer range-bus balance.
    for table,trace in zip(spec['air']['tables'],packed):
        for i,row in enumerate(trace):
            for j,e in enumerate(table['constraints']):
                assert eval_expr(e,row,trace[(i+1)%len(trace)],spec['public'],i==0,i+1==len(trace))==0,(i,j)
    assert sum(sum(row[8+i]<<i for i in range(16)) for row in table_rows)==sum(all_counts.values())
    return spec,packed,dict(code_count_column=maps[1][lit.COUNT],tables=rewrites,range_rows=256,
        range_lookups=sum(all_counts.values()),max_range_multiplicity=max(all_counts.values()),formal_refinement_proved=False)
