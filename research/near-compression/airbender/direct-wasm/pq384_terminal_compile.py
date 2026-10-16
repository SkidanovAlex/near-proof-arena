"""Verifier-derived concrete canonical AIR-terminal circuit compiler.

No witness values or private evaluations enter compilation. Public constants
may fold; the caller derives all terminal metadata and batching rho.
"""
import sys
from check_whir_handoff import add,sub,mul
from native_folded_v2 import compile_weighted
from table_constraint_whir import selectors
from pq384_shift import eq_point
import pq384_global_bus as bus


def compile_terminal(spec,alpha,gamma,finals,terminals,rho):
    sys.setrecursionlimit(100000)
    widths=[t['width']+4*bus.aux.layout(t)['aux_columns'] for t in spec['air']['tables']]
    blocks=[];offset=0;placement={}
    for ti in sorted(range(len(widths)),key=lambda i:(-(1<<(widths[i]-1).bit_length()),i)):
        W=1<<(widths[ti]-1).bit_length();placement[ti]=(offset,W);blocks.append(dict(table=ti,offset=offset,column_capacity=W,block_size=2*W));offset+=2*W
    private_capacity=1<<(offset-1).bit_length()
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
    outputs=[]
    for ti,(table,terminal) in enumerate(zip(spec['air']['tables'],terminals)):
        point=terminal['point'];mixing=terminal['mixing'];tau=terminal['tau'];sels=selectors(point)
        program=compile_weighted(table,spec['public'],alpha,gamma,[bus.ext(v) for v in finals[ti]],mixing,bus)
        ins=[tuple(program[i:i+7]) for i in range(0,len(program),7)];uses=[0]*len(ins)
        for code,x,y,*_ in ins:
            if code in (6,7,8):uses[x]+=1;uses[y]+=1
        local={};base,W=placement[ti]
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
        output=op('mul',rebuild(len(ins)-1),const(eq_point(tau,point)));outputs.append((output,terminal["claim"]))
    power=bus.ONE;terms=[]
    for output,target in outputs:
        terms.append((op('mul',const(power),op('sub',output,const(target))),1));power=mul(power,rho)
    root=balanced(terms)
    # A public-constant terminal still gets one explicit layer (no witness premise).
    if nodes[root][0] in ('const','input'):root=emit(('add',root,zero))
    live=set();stack=[root]
    while stack:
        i=stack.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):stack.extend(nodes[i][1:])
    return dict(nodes=nodes,live_nodes=sorted(live),root=root,input_blocks=blocks,private_input_capacity=private_capacity)
