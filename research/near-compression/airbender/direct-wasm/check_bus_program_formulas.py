"""Exact ordered auxiliary formula/register certificates for active group1.
No inverses: square chains, multiplicity products, first/link/last boundaries.
"""
import argparse,copy,hashlib,json,sys,time
from pathlib import Path
from check_terminal_dag_certificates import require
from check_terminal_rebuild_certificates import capture
from check_air_program_certificates import valid_program,accumulation

def lit(x):return ['lit',list(x)]
def plus(a,b):return ['add',a,b]
def minus(a,b):return ['sub',a,b]
def times(a,b):return ['mul',a,b]

def expr(e,public):
    op=e[0]
    if op=='c':return lit(base(e[1]))
    if op=='p':return lit(base(public[e[1]] if e[1]<len(public) else 0))
    if op=='v':return ['next' if e[2] else 'current',e[1]]
    if op in ('first','last','trans'):return [op]
    if op=='-':return minus(lit(ZERO),expr(e[1],public))
    return (plus if op=='+' else times)(expr(e[1],public),expr(e[2],public))

def expected(table,public,alpha,gamma,finals):
    interactions=table['interactions'];chains=sum(2*max(0,len(i['mult'])-1) for i in interactions)
    order=[i for i,x in enumerate(interactions) if x['send']]+[i for i,x in enumerate(interactions) if not x['send']]
    require(len(finals)==len(order),'final shape');width=table['width'];residuals=[];factors=[];offset=0
    def aux(index,nxt=False):
        value=lit(ZERO)
        for j,basis in enumerate(BASIS):value=plus(value,times(['next' if nxt else 'current',width+4*index+j],lit(basis)))
        return value
    for ii,interaction in enumerate(interactions):
        fp=lit(ZERO);weight=ONE
        for e in interaction['msg']:fp=plus(fp,times(expr(e,public),lit(weight)));weight=mul(weight,alpha)
        fp=plus(fp,lit(mul(base(interaction['bus']+1),weight)));p0=minus(lit(gamma),fp);bits=[expr(e,public) for e in interaction['mult']]
        if not bits:factors.append(lit(ONE));continue
        first=plus(lit(ONE),times(bits[0],minus(p0,lit(ONE))))
        if len(bits)==1:factors.append(first);continue
        k=len(bits)-1;ps=[aux(offset+j) for j in range(k)];pis=[aux(offset+k+j) for j in range(k)]
        for j in range(k):
            prev=p0 if j==0 else ps[j-1]
            residuals.append(dict(kind='square',interaction=ii,step=j,formula=minus(ps[j],times(prev,prev))))
        for j in range(k):
            prev=first if j==0 else pis[j-1]
            residuals.append(dict(kind='multiplicity-link',interaction=ii,step=j,formula=minus(pis[j],times(prev,plus(lit(ONE),times(bits[j+1],minus(ps[j],lit(ONE))))))))
        factors.append(pis[-1]);offset+=2*k
    require(offset==chains,'chain offset')
    for j,ii in enumerate(order):
        a,an=aux(offset+j),aux(offset+j,True);factor=times(a,factors[ii])
        for kind,formula in [('first',times(['first'],minus(a,lit(ONE)))),('transition',times(['trans'],minus(an,factor))),('last',times(['last'],minus(factor,lit(finals[j]))))]:
            residuals.append(dict(kind=kind,interaction=ii,accumulator=j,formula=formula))
    return residuals,chains+len(order)

def validate_formula(formula,index,ins,width,counts):
    require(type(index)is int and 0<=index<len(ins),'formula register index');op=formula[0];row=ins[index];counts[op]=counts.get(op,0)+1
    if op=='lit':require(row==[0,0,0,*formula[1]],'literal formula')
    elif op in ('current','next'):
        require(type(formula[1])is int and 0<=formula[1]<width,'aux column bound')
        require(row==[1 if op=='current' else 2,formula[1],0,0,0,0,0],'coordinate formula')
    elif op in ('first','last','trans'):require(row==[{'first':3,'last':4,'trans':5}[op],0,0,0,0,0,0],'boundary selector')
    else:
        require(op in ('add','sub','mul') and len(formula)==3,'formula shape');require(row[0]=={'add':6,'sub':7,'mul':8}[op] and row[3:]==[0]*4,'arithmetic formula')
        validate_formula(formula[1],row[1],ins,width,counts);validate_formula(formula[2],row[2],ins,width,counts)

def main():
    global ZERO,ONE,base,mul,BASIS
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--capture',action='append',required=True);ap.add_argument('--rebuild-dir',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();sys.path.insert(0,a.reference_dir)
    from verify_whir_toy import P,ZERO,ONE,base,mul
    import check_air_program_certificates as abi
    abi.P=P;abi.ZERO=ZERO
    from native_folded_v2 import compile_weighted
    import pq384_global_bus as bus
    BASIS=bus.BASIS;out=Path(a.output);out.mkdir(parents=True,exist_ok=True);reports=[]
    synthetic=[]
    for k in (0,1,2,4):
        table={'width':1,'constraints':[],'interactions':[
          {'send':False,'bus':0,'msg':[['v',0,0]],'mult':[['v',0,0]]*k},
          {'send':True,'bus':1,'msg':[['v',0,1],['c',7]],'mult':[['v',0,1]]}]}
        for zero_case in (True,False):
            alpha=ZERO if zero_case else (2,3,5,7);gamma=ZERO if zero_case else (11,13,17,19)
            finals=[ZERO,(23,29,31,37)];fresh=compile_weighted(table,[],alpha,gamma,finals,(41,43,47,53),bus)
            ins=[list(fresh[i:i+7]) for i in range(0,len(fresh),7)];valid_program(ins)
            formulas,aw=expected(table,[],alpha,gamma,finals);roots=[x['residual'] for x in accumulation(ins)['steps'][len(bus.constraints(table)):]]
            require(len(formulas)==len(roots),'synthetic residual count')
            kinds={};synthetic_negative=0
            for rec,index in zip(formulas,roots):
                validate_formula(rec['formula'],index,ins,1+4*aw,{});kinds[rec['kind']]=kinds.get(rec['kind'],0)+1
                bad=copy.deepcopy(rec['formula']);bad[0]='add'
                try:validate_formula(bad,index,ins,1+4*aw,{})
                except ValueError:synthetic_negative+=1
                else:raise AssertionError('accepted synthetic wrong formula')
            current=[ZERO if zero_case else tuple((i*97+j*19+1)%P for j in range(4)) for i in range(1+4*aw)]
            nxt=[ZERO if zero_case else tuple((i*89+j*23+2)%P for j in range(4)) for i in range(1+4*aw)]
            sels={'first':(2,1,0,0),'last':(3,0,1,0),'trans':(5,0,0,1)};registers=[]
            for op,x,y,*constant in ins:
                if op==0:value=tuple(constant)
                elif op==1:value=current[x]
                elif op==2:value=nxt[x]
                elif op in (3,4,5):value=sels[{3:'first',4:'last',5:'trans'}[op]]
                else:value={6:bus.add,7:bus.sub,8:bus.mul}[op](registers[x],registers[y])
                registers.append(value)
            reconstructed=bus.algebra.reconstruct(current[1:]);next_reconstructed=bus.algebra.reconstruct(nxt[1:])
            expected_values=bus.aux.evaluate(table,current[:1],nxt[:1],[],sels,alpha,gamma,reconstructed,next_reconstructed,finals)
            require([registers[i] for i in roots]==expected_values,'synthetic independent aux.evaluate parity')
            synthetic.append(dict(bits=k,zero_case=zero_case,kinds=kinds,residuals=len(roots),value_comparisons=len(roots),negative_checks=synthetic_negative))
    for path in map(Path,a.capture):
        started=time.perf_counter();_,profile,args=capture(path);spec,alpha,gamma,finals,terminals,rho=args
        source=Path(a.rebuild_dir)/(path.name+'-rebuild.json');rebuild=json.loads(source.read_text());require(len(rebuild['programs'])==len(spec['air']['tables'])==len(terminals),'table count')
        tables=[];kinds={};counts={};negative=0;bitcases={}
        for ti,(table,program,terminal) in enumerate(zip(spec['air']['tables'],rebuild['programs'],terminals)):
            ins=program['instructions'];valid_program(ins);fresh=compile_weighted(table,spec['public'],alpha,gamma,[tuple(x) for x in finals[ti]],terminal['mixing'],bus)
            require(ins==[list(fresh[i:i+7]) for i in range(0,len(fresh),7)],'fresh program binding')
            formulas,aw=expected(table,spec['public'],alpha,gamma,finals[ti]);require(aw==bus.aux.layout(table)['aux_columns'],'aux layout')
            for interaction in table['interactions']:
                k=len(interaction['mult']);bitcases[str(k)]=bitcases.get(str(k),0)+1
            roots=[s['residual'] for s in accumulation(ins)['steps'][len(bus.constraints(table)):]]
            require(len(roots)==len(formulas),'residual coverage/order')
            for record,index in zip(formulas,roots):
                validate_formula(record['formula'],index,ins,table['width']+4*aw,counts);record['register']=index;kinds[record['kind']]=kinds.get(record['kind'],0)+1
                bad=copy.deepcopy(record['formula']);bad[0]='add'
                try:validate_formula(bad,index,ins,table['width']+4*aw,{})
                except ValueError:negative+=1
                else:raise AssertionError('accepted wrong residual operation')
            tables.append(dict(table=ti,auxiliary_columns=aw,residuals=formulas))
        raw=json.dumps(dict(profile=profile,program_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),tables=tables),separators=(',',':')).encode();dest=out/(path.name+'-bus-program.json');dest.write_bytes(raw)
        report=dict(profile=profile,capture=str(path),kinds=kinds,formula_nodes=counts,interaction_bit_lengths=bitcases,negative_checks=negative,artifact=str(dest),sha256=hashlib.sha256(raw).hexdigest(),seconds=time.perf_counter()-started)
        reports.append(report);print(json.dumps(report),flush=True);(out/'report.json').write_text(json.dumps(dict(status='PASS',synthetic=synthetic,captures=reports,scope='Executable group1 formula/register validation; no inverse gates in this profile. Not kernel capture proofs or randomized bus-balance security.'),indent=2))
if __name__=='__main__':main()
