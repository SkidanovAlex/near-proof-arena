"""Source Expr/register and ordered residual accumulation certificates.
Checks actual seven-word programs, without executing witness values.
Auxiliary residual formula→bus AIR equivalence remains separate.
"""
import argparse,copy,hashlib,json,sys,time
from pathlib import Path
from check_terminal_dag_certificates import require
from check_terminal_rebuild_certificates import capture

def valid_program(ins):
    for i,row in enumerate(ins):
        require(len(row)==7 and all(type(x)is int and 0<=x<1<<32 for x in row),'ABI seven u32 words')
        op,x,y,*constant=row;require(op<9 and all(c<P for c in constant),'opcode/canonical field')
        if op>=6:require(x<i and y<i,'acyclic ABI')

def check_expr(e,i,ins,public,width,counts=None):
    require(type(i)is int and 0<=i<len(ins),'expression register index')
    require(isinstance(e,list) and e,'Expr list');op=e[0];row=ins[i]
    require(len(e)==({'c':2,'p':2,'v':3,'first':1,'last':1,'trans':1,'+':3,'*':3,'-':2}.get(op,0)),'Expr shape')
    if counts is not None:counts[op]=counts.get(op,0)+1
    if op=='c':require(type(e[1])is int and e[1]>=0,'natural constant');require(row==[0,0,0,*base(e[1])],'constant route')
    elif op=='p':require(type(e[1])is int and e[1]>=0,'public index');require(row==[0,0,0,*base(public[e[1]] if e[1]<len(public) else 0)],'public route')
    elif op=='v':
        require(type(e[1])is int and 0<=e[1]<width and type(e[2])is int and e[2] in (0,1),'source column')
        require(row==[2 if e[2] else 1,e[1],0,0,0,0,0],'current/next route')
    elif op in ('first','last','trans'):require(row==[{'first':3,'last':4,'trans':5}[op],0,0,0,0,0,0],'selector route')
    elif op in ('+','*'):
        require(row[0]==(6 if op=='+' else 8) and row[3:]==[0]*4,'binary opcode')
        check_expr(e[1],row[1],ins,public,width,counts);check_expr(e[2],row[2],ins,public,width,counts)
    elif op=='-':
        require(row[0]==7 and row[3:]==[0]*4 and ins[row[1]]==[0,0,0,*ZERO],'negation zero register')
        check_expr(e[1],row[2],ins,public,width,counts)
    else:raise ValueError('source expression kind')

def locate_expr(e,lookup,public):
    op=e[0]
    if op=='c':key=(0,0,0,*base(e[1]))
    elif op=='p':key=(0,0,0,*base(public[e[1]] if e[1]<len(public) else 0))
    elif op=='v':key=(2 if e[2] else 1,e[1],0,0,0,0,0)
    elif op in ('first','last','trans'):key=({'first':3,'last':4,'trans':5}[op],0,0,0,0,0,0)
    elif op in ('+','*'):key=(6 if op=='+' else 8,locate_expr(e[1],lookup,public),locate_expr(e[2],lookup,public),0,0,0,0)
    elif op=='-':key=(7,lookup[(0,0,0,*ZERO)],locate_expr(e[1],lookup,public),0,0,0,0)
    else:raise ValueError('source Expr')
    return lookup[key]

def accumulation(ins):
    require(ins[-1][0]==6 and ins[-1][3:]==[0]*4,'finish add')
    total,zero=ins[-1][1:3];require(ins[zero]==[0,0,0,*ZERO],'finish zero')
    chain=[];cursor=total
    while cursor!=zero:
        op,previous,product,*unused=ins[cursor];require(op==6 and unused==[0]*4,'accumulation add')
        op,coefficient,residual,*unused=ins[product];require(op==8 and unused==[0]*4,'accumulation product')
        require(ins[coefficient][:3]==[0,0,0],'mixing coefficient constant')
        chain.append(dict(previous=previous,coefficient=coefficient,residual=residual,product=product,result=cursor));cursor=previous
    return dict(zero=zero,total=total,output=len(ins)-1,steps=chain[::-1])

def check_accumulation(ins,cert,mixing):
    zero=cert['zero'];require(type(zero)is int and 0<=zero<len(ins) and ins[zero]==[0,0,0,*ZERO],'accumulator zero')
    cursor=zero;power=ONE
    for step in cert['steps']:
        require(set(step)=={'previous','coefficient','residual','product','result'},'accumulator fields')
        require(all(type(v)is int and 0<=v<len(ins) for v in step.values()),'accumulator register index')
        require(step['previous']==cursor,'accumulator continuity')
        require(ins[step['coefficient']]==[0,0,0,*power],'ordered mixing power')
        require(ins[step['product']]==[8,step['coefficient'],step['residual'],0,0,0,0],'weighted residual multiply')
        require(ins[step['result']]==[6,cursor,step['product'],0,0,0,0],'weighted residual add')
        cursor=step['result'];power=mul(power,mixing)
    require(cert['total']==cursor and cert['output']==len(ins)-1 and ins[-1]==[6,cursor,zero,0,0,0,0],'final register copy')

def main():
    global P,ZERO,ONE,base,mul
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--capture',action='append',required=True);ap.add_argument('--rebuild-dir',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();sys.path.insert(0,a.reference_dir)
    from verify_whir_toy import P,ZERO,ONE,base,mul
    from native_folded_v2 import compile_weighted
    import pq384_global_bus as bus
    out=Path(a.output);out.mkdir(parents=True,exist_ok=True);reports=[]
    fixture_exprs=[['c',P+1],['p',0],['p',100],['v',0,0],['v',0,1],['first'],['last'],['trans'],['-',['v',0,0]],['+',['v',0,0],['v',0,1]],['*',['v',0,0],['p',100]]]
    fixture={'width':1,'constraints':fixture_exprs,'interactions':[]}
    fresh=compile_weighted(fixture,[7],ONE,ONE,[],ONE,bus);fi=[list(fresh[i:i+7]) for i in range(0,len(fresh),7)];lookup={}
    for i,row in enumerate(fi):lookup.setdefault(tuple(row),i)
    for e in fixture_exprs:check_expr(e,locate_expr(e,lookup,[7]),fi,[7],1)
    fi_bad=copy.deepcopy(fi);reg=locate_expr(['v',0,1],lookup,[7]);fi_bad[reg][0]=1
    try:check_expr(['v',0,1],reg,fi_bad,[7],1)
    except ValueError:pass
    else:raise AssertionError('accepted next/current substitution')
    for path in map(Path,a.capture):
        started=time.perf_counter();_,profile,args=capture(path);spec,alpha,gamma,finals,terminals,rho=args
        source=Path(a.rebuild_dir)/(path.name+'-rebuild.json');rebuild=json.loads(source.read_text());tables=[];counts={};negative=0
        require(len(spec['air']['tables'])==len(rebuild['programs'])==len(terminals),'complete table coverage')
        for ti,(table,program,terminal) in enumerate(zip(spec['air']['tables'],rebuild['programs'],terminals)):
            ins=program['instructions'];valid_program(ins);lookup={}
            fresh=compile_weighted(table,spec['public'],alpha,gamma,[tuple(x) for x in finals[ti]],terminal['mixing'],bus)
            require(ins==[list(fresh[i:i+7]) for i in range(0,len(fresh),7)],'fresh compile_weighted binding')
            for i,row in enumerate(ins):lookup.setdefault(tuple(row),i)
            constraints=bus.constraints(table);expressions=list(constraints)
            for interaction in table['interactions']:expressions.extend(interaction['msg']);expressions.extend(interaction['mult'])
            routes=[]
            for e in expressions:
                i=locate_expr(e,lookup,spec['public']);check_expr(e,i,ins,spec['public'],table['width'],counts);routes.append(dict(expr=e,register=i))
            for bad_index in (-1,True,len(ins)):
                try:check_expr(expressions[0],bad_index,ins,spec['public'],table['width'])
                except ValueError:negative+=1
                else:raise AssertionError('accepted bad Expr register index')
            acc=accumulation(ins);check_accumulation(ins,acc,terminal['mixing'])
            require([r['register'] for r in routes[:len(constraints)]]==[s['residual'] for s in acc['steps'][:len(constraints)]],'constraint residual order')
            for label,mutate in [('mix-order',lambda c:c['steps'][0].__setitem__('coefficient',c['zero'])),('finish-copy',lambda c:c.__setitem__('output',0)),('negative-index',lambda c:c['steps'][0].__setitem__('residual',-1))]:
                if not acc['steps']:continue
                bad=copy.deepcopy(acc);mutate(bad)
                try:check_accumulation(ins,bad,terminal['mixing'])
                except ValueError:negative+=1
                else:raise AssertionError('accepted '+label)
            tables.append(dict(table=ti,expression_routes=routes,source_constraints=len(constraints),accumulation=acc,auxiliary_residual_count=len(acc['steps'])-len(constraints)))
        raw=json.dumps(dict(profile=profile,program_artifact=str(source),program_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),tables=tables),separators=(',',':')).encode();dest=out/(path.name+'-air-program.json');dest.write_bytes(raw)
        report=dict(profile=profile,capture=str(path),tables=len(tables),expression_nodes=counts,expression_roots=sum(len(t['expression_routes']) for t in tables),residuals=sum(len(t['accumulation']['steps']) for t in tables),auxiliary_residuals=sum(t['auxiliary_residual_count'] for t in tables),negative_checks=negative,artifact=str(dest),sha256=hashlib.sha256(raw).hexdigest(),seconds=time.perf_counter()-started)
        reports.append(report);print(json.dumps(report),flush=True);(out/'report.json').write_text(json.dumps(dict(status='PASS',synthetic_expr_routes=len(fixture_exprs),synthetic_next_current_rejected=True,captures=reports,scope='Executable AST and mixing structural validation; auxiliary residual formula correspondence and kernel capture proofs remain separate.'),indent=2))
if __name__=='__main__':main()
