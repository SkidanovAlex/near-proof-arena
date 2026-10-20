"""Fixed Boolean wiring predicate -> shared Shannon evaluation DAG.

The index order is fixed by the verifier, never supplied by the prover.
Terminal 1 means every remaining Boolean assignment is in the wiring set.
"""


def variable_order(n,m,kind):
    axes=[list(range(n)),list(range(n,n+m)),list(range(n+m,n+2*m))]
    if kind.startswith('interleaved'):
        parts=kind.split('_')
        permutation=parts[1] if len(parts)>1 else '012'
        assert sorted(permutation)==list('012')
        bits=range(max(n,m)-1,-1,-1) if len(parts)>2 and parts[2]=='high' else range(max(n,m))
        return [axes[int(k)][i] for i in bits for k in permutation if i<len(axes[int(k)])]
    if kind=='inputs_first':return axes[1]+axes[2]+axes[0]
    if kind=='output_first':return axes[0]+axes[1]+axes[2]
    raise ValueError(kind)


def build(keys,order):
    keys=set(keys);nodes=[None,None];intern={}
    assert all(0<=k<1<<len(order) for k in keys)
    assert sorted(order)==list(range(len(order)))
    def go(ks,level):
        if not ks:return 0
        if len(ks)==1<<(len(order)-level):return 1
        bit=order[level];mask=1<<bit
        low=go({k for k in ks if not k&mask},level+1)
        high=go({k^mask for k in ks if k&mask},level+1)
        if low==high:return low
        node=(bit,low,high)
        if node not in intern:intern[node]=len(nodes);nodes.append(node)
        return intern[node]
    root=go(keys,0)
    return nodes,root


def evaluate(c,nodes,root,point):
    values=[c.zero,c.one]
    for bit,low,high in nodes[2:]:
        a,b=values[low],values[high]
        if b==c.zero:values.append(c.mul(c.sub(c.one,point[bit]),a))
        else:values.append(c.add(a,c.mul(point[bit],c.sub(b,a))))
    return values[root]


def wiring(c,gates,queries,ru,rv,a,b,kind):
    n=(len(gates)-1).bit_length();m=len(ru)
    assert len(rv)==m
    order=variable_order(n,m,kind)
    coeff=[]
    for op in ('add','sub','mul'):
        keys=[k+(i<<n)+(j<<(n+m)) for k,(tag,i,j) in enumerate(gates) if tag==op]
        nodes,root=build(keys,order)
        terms=[c.mul(scale,evaluate(c,nodes,root,list(q)+ru+rv)) for q,scale in queries]
        coeff.append(c.mul(c.sum(terms),c.op(op,a,b)))
    return c.sum(coeff)
