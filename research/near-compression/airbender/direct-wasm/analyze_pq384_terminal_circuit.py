"""Reviewable canonical AIR-terminal DAG and conservative layered-GKR budget.

No proof protocol is implemented. Canonical Expr + all group1 auxiliary DAGs
come from existing native compiler. Actual selectors/public/challenges are public
constants. Associative add/sub chains are balanced only through singly-used
nodes; constants fold symbolically, never private input values. Exact actual
outputs are crosschecked against independent canonical AIR evaluator.
"""
import argparse,collections,copy,hashlib,json,math,sys
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--proof-directory',required=True);ap.add_argument('--output-directory',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir);sys.setrecursionlimit(100000)
    import pq384_global_bus as bus
    from native_folded_v2 import compile_weighted
    from check_whir_handoff import add,sub,mul
    from table_constraint_whir import selectors
    from pq384_primitives import P
    from pq384_shift import eq_point
    source=Path(a.proof_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    trusted=json.loads((source/'statement.json').read_text());proof=json.loads((source/'proof.json').read_text());spec=trusted['spec'];roots=[bytes.fromhex(v) for v in trusted['roots']]
    widths=[t['width']+4*bus.aux.layout(t)['aux_columns'] for t in spec['air']['tables']]
    blocks=[];offset=0;placement={}
    for ti in sorted(range(len(widths)),key=lambda i:(-(1<<(widths[i]-1).bit_length()),i)):
        W=1<<(widths[ti]-1).bit_length();placement[ti]=(offset,W);blocks.append(dict(table=ti,offset=offset,column_capacity=W,block_size=2*W));offset+=2*W
    private_capacity=1<<(offset-1).bit_length();inputs=[bus.ZERO]*private_capacity
    nodes=[];cache={}
    def emit(key):
        if key not in cache:cache[key]=len(nodes);nodes.append(key)
        return cache[key]
    def const(v):return emit(('const',*v))
    zero=const(bus.ZERO);one=const(bus.ONE)
    def op(kind,x,y):
        nx,ny=nodes[x],nodes[y]
        if nx[0]==ny[0]=='const':return const({'add':add,'sub':sub,'mul':mul}[kind](nx[1:],ny[1:]))
        if kind=='add':
            if x==zero:return y
            if y==zero:return x
        if kind=='sub':
            if y==zero:return x
            if x==y:return zero
        if kind=='mul':
            if x==zero or y==zero:return zero
            if x==one:return y
            if y==one:return x
        return emit((kind,x,y))
    def balanced(terms):
        if not terms:return zero
        while len(terms)>1:
            nxt=[]
            for i in range(0,len(terms),2):
                if i+1==len(terms):nxt.append(terms[i]);continue
                x,s=terms[i];y,t=terms[i+1]
                if s==t:nxt.append((op('add',x,y),s))
                elif s==1:nxt.append((op('sub',x,y),1))
                else:nxt.append((op('sub',y,x),1))
            terms=nxt
        v,sign=terms[0];return v if sign==1 else op('sub',zero,v)
    st,tr,alpha,gamma=bus.begin(spec,roots);ars=[bytes.fromhex(v) for v in proof['aux_roots']];bus.initialize_aux(tr,spec,ars,proof['finals'])
    tables=[];outputs=[];raw_total=0;raw_maxdepth=0
    for ti,(table,part) in enumerate(zip(spec['air']['tables'],proof['tables'])):
        n=spec['log_rows'][ti];t=copy.deepcopy(tr);mixing,tau=bus.table_start(t,ti,n);point=[];target=bus.ZERO
        for rd in part['constraint_rounds']:
            t.commit_ext(rd);r=t.draw(1,True)[0];point.append(r);target=bus.poly([bus.ext(v) for v in rd],r)
        bus.verify_table_reduction(part,spec,st,tr,alpha,gamma,ti,proof['finals'][ti],[roots[ti],ars[ti]])
        current=[bus.ext(v) for v in part['shift_reduction']['current_evals']];nxt=[bus.ext(v) for v in part['shift_reduction']['next_evals']]
        fs=[bus.ext(v) for v in proof['finals'][ti]];sels=selectors(point)
        expected=bus.weighted(spec,ti,alpha,gamma,fs,mixing,tau,point,current,nxt);assert expected==target
        program=compile_weighted(table,spec['public'],alpha,gamma,fs,mixing,bus)
        ins=[tuple(program[i:i+7]) for i in range(0,len(program),7)];uses=[0]*len(ins);depth=[];rawvalues=[]
        for instruction in ins:
            code,x,y,*c=instruction
            if code in (6,7,8):uses[x]+=1;uses[y]+=1;depth.append(1+max(depth[x],depth[y]));rawvalues.append({6:add,7:sub,8:mul}[code](rawvalues[x],rawvalues[y]))
            else:
                depth.append(0);rawvalues.append(tuple(c) if code==0 else current[x] if code==1 else nxt[x] if code==2 else sels[{3:'first',4:'last',5:'trans'}[code]])
        assert mul(eq_point(tau,point),rawvalues[-1])==expected
        local={};start_nodes=len(nodes);base,W=placement[ti]
        for col,v in enumerate(current):inputs[base+col]=v
        for col,v in enumerate(nxt):inputs[base+W+col]=v
        def rebuild(i):
            if i in local:return local[i]
            code,x,y,*c=ins[i]
            if code==0:result=const(tuple(c))
            elif code in (1,2):result=emit(('input',base+x+(W if code==2 else 0)))
            elif code in (3,4,5):result=const(sels[{3:'first',4:'last',5:'trans'}[code]])
            elif code in (6,7):
                terms=[]
                def collect(k,sign,root=False):
                    opcode,left,right,*_=ins[k]
                    if opcode in (6,7) and (root or uses[k]==1):
                        collect(left,sign);collect(right,sign if opcode==6 else -sign)
                    else:terms.append((rebuild(k),sign))
                collect(i,1,True);result=balanced(terms)
            elif code==8:result=op('mul',rebuild(x),rebuild(y))
            else:raise AssertionError('unknown compiler instruction')
            local[i]=result;return result
        output=op('mul',rebuild(len(ins)-1),const(eq_point(tau,point)));outputs.append((output,target))
        tables.append(dict(table=ti,width=widths[ti],raw_instructions=len(ins),raw_depth=depth[-1],balanced_new_nodes=len(nodes)-start_nodes,
                           output=output,target=target,point=point,mixing=mixing,tau=tau,
                           compiler_sha256=hashlib.sha256(bytes(program)).hexdigest(),source_constraints=len(bus.constraints(table)),auxiliary_residuals=3*bus.aux.layout(table)['finals']+bus.aux.layout(table)['chain_columns']))
        raw_total+=len(ins);raw_maxdepth=max(raw_maxdepth,depth[-1])
    # Resource model: one public output-batching coefficient, not a new protocol.
    rho=(7,11,13,17);power=bus.ONE;terms=[]
    for output,target in outputs:
        terms.append((op('mul',const(power),op('sub',output,const(target))),1));power=mul(power,rho)
    root=balanced(terms)
    values=[];levels=[];max_use=[0]*len(nodes)
    for i,node in enumerate(nodes):
        kind=node[0]
        if kind=='const':values.append(tuple(node[1:]));levels.append(0)
        elif kind=='input':values.append(inputs[node[1]]);levels.append(0)
        else:
            _,x,y=node;assert x<i and y<i
            values.append({'add':add,'sub':sub,'mul':mul}[kind](values[x],values[y]));levels.append(1+max(levels[x],levels[y]));max_use[x]=max(max_use[x],levels[-1]);max_use[y]=max(max_use[y],levels[-1])
    assert values[root]==bus.ZERO
    for output,target in outputs:assert values[output]==target
    # Drop unreachable construction intermediates created during constant folding.
    live=set();stack=[root]
    while stack:
        i=stack.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):stack.extend(nodes[i][1:])
    max_use=[0]*len(nodes)
    for i in live:
        if nodes[i][0] in ('add','sub','mul'):
            for x in nodes[i][1:]:max_use[x]=max(max_use[x],levels[i])
    counts=collections.Counter(levels[i] for i in live);relays=0
    for i in live:
        for level in range(levels[i]+1,max_use[i]):counts[level]+=1;relays+=1
    layer_widths=[counts[level] for level in range(levels[root]+1)]
    # Standard fan-in2 layer sumcheck:2log(prevwidth) rounds,3 field coefficients.
    # Includes2 terminal input evals/layer. Optional line reduction costs m+1 coeffs.
    layer_reports=[];batch_bytes=line_bytes=0
    for level in range(1,len(layer_widths)):
        m=(max(1,layer_widths[level-1])-1).bit_length();core=96*m+32
        batch_bytes+=core;line_bytes+=core+16*(m+1)
        layer_reports.append(dict(level=level,width=layer_widths[level],previous_log_width=m,
                                  sumcheck_rounds=2*m,batch_two_claims_bytes=core,line_reduction_bytes=core+16*(m+1)))
    artifact=dict(format='near-terminal-circuit-analysis-v1',nodes=nodes,root=root,live_nodes=sorted(live),input_blocks=blocks,
                  private_input_capacity=private_capacity,public_batch_rho=rho,tables=tables)
    (out/'circuit.json').write_text(json.dumps(artifact,separators=(',',':')))
    (out/'input-values.json').write_text(json.dumps(inputs,separators=(',',':')))
    report=dict(status='PASS',actual_tables=len(tables),actual_terminal_values_checked=sum(2*w for w in widths),
        raw_compiler_instructions=raw_total,raw_max_table_depth=raw_maxdepth,balanced_live_nodes=len(live),
        balanced_depth=levels[root],constant_nodes=sum(nodes[i][0]=='const' for i in live),
        private_input_nodes=sum(nodes[i][0]=='input' for i in live),private_input_capacity=private_capacity,
        relay_copy_nodes=relays,layered_nodes=len(live)+relays,max_layer_width=max(layer_widths),layer_widths=layer_widths,
        gkr_batch_two_claims_transport_bytes=batch_bytes,gkr_line_reduction_transport_bytes=line_bytes,
        source_statement_sha256=hashlib.sha256((source/'statement.json').read_bytes()).hexdigest(),
        circuit_sha256=hashlib.sha256((out/'circuit.json').read_bytes()).hexdigest(),
        cost_assumptions=['Ext4 is16bytes; quadratic message is3elements','Generic binary layer relation sums over2*log(previouswidth) variables',
          'Two-claim batching requires new proof theorem/transcript; line option adds m+1 coefficients perlayer',
          'Public wiring evaluation/sparse sumcheck algorithm not implemented','Final circuit input claims need generalized current/shifted coefficient-weight PCS; excluded from GKR byte estimates',
          'Circuit constantfolding uses publicconstants only; oldproof evaluations are used solely for parity checks',
          'No cryptographic security or formal compiler refinement claim'],layers=layer_reports)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('layers','layer_widths')},indent=2))

if __name__=='__main__':main()
