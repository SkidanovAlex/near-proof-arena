"""Ext8 dual Mobius coefficient weights for GKR current/cyclic-next inputs.

Functions implement the final opening obligation, not its PCS proof. No
individual source claims are accepted: weights come from verifier GKR queries.
"""
from pq384_ext8_terminal_gkr import eqs,add,sub,mul,ZERO,ONE,mle


def upper_zeta(v):
    out=list(v);bit=1
    while bit<len(out):
        for i in range(len(out)):
            if not i&bit:out[i]=add(out[i],out[i|bit])
        bit*=2
    return out


def row_weights(point):
    e=eqs(point);shift=[e[(i-1)%len(e)] for i in range(len(e))]
    return upper_zeta(e),upper_zeta(shift)


def lane_weights(point,current_columns,next_columns):
    a,b=upper_zeta(current_columns),upper_zeta(next_columns);r,s=row_weights(point)
    return [add(mul(x,y),mul(z,t)) for x,z in zip(a,b) for y,t in zip(r,s)]


def row_weight_mles(point,u):
    """Current monomials and shifted monomials at coefficient Boolean point u.

Borrow DP computes eq(point,row-1) times product(1-u_i) over zero row bits.
Final borrow is discarded because subtraction wraps modulo2^n.
"""
    assert len(point)==len(u)
    current=ONE;no_borrow=ZERO;borrow=ONE
    for r,x in zip(point,u):
        a=sub(ONE,x)
        current=mul(current,add(a,mul(x,r)))
        no_borrow,borrow=(add(mul(no_borrow,add(mul(sub(ONE,r),a),r)),mul(borrow,sub(ONE,r))),mul(borrow,mul(r,a)))
    return current,add(no_borrow,borrow)


def lane_weight_mle(point,current_columns,next_columns,u):
    n=len(point);a,b=row_weight_mles(point,u[:n])
    return add(mul(a,mle(upper_zeta(current_columns),u[n:])),mul(b,mle(upper_zeta(next_columns),u[n:])))


def branch_lanes(block,branch_offset,width,packing,input_weights):
    """Read exact final GKR slot weights; padding columns are zero."""
    start=block['offset']+branch_offset;W=block['column_capacity']
    return [([input_weights[start+c] if c<width else ZERO for c in range(j,j+packing)],
             [input_weights[start+W+c] if c<width else ZERO for c in range(j,j+packing)])
            for j in range(0,width,packing)]


def opening_branches(spec,terminals,circuit,input_weights):
    """Derive source and auxiliary lanes from trusted circuit placement.

    These descriptors deliberately omit roots: the caller must bind each to
    its actual polynomial commitment before they can be PCS statements.
    """
    import bus_auxiliary
    from pq384_primitives import require
    from pq384_ext8_reference import canonical
    require(len(terminals)==len(spec['air']['tables']),'terminal count')
    require(len(input_weights)==circuit['private_input_capacity'],'input weights')
    input_weights=[canonical(w) for w in input_weights]
    blocks={b['table']:b for b in circuit['input_blocks']}
    require(len(blocks)==len(spec['air']['tables']),'block count')
    result=[]
    for ti,table in enumerate(spec['air']['tables']):
        source_width=table['width'];aux_width=8*bus_auxiliary.layout(table)['aux_columns']
        block=blocks[ti]
        require(block['column_capacity']>=source_width+aux_width,'column capacity')
        require(0<=block['offset'] and block['offset']+2*block['column_capacity']<=len(input_weights),'block bounds')
        point=[canonical(v) for v in terminals[ti]['point']]
        require(len(point)==spec['log_rows'][ti],'row point')
        for branch,width,offset,key in ((0,source_width,0,'source_packings'),(1,aux_width,source_width,'aux_packings')):
            if not width:continue
            packing=spec[key][ti]
            require(type(packing)is int and packing>0 and packing&(packing-1)==0,'packing')
            result.append(dict(table=ti,branch=branch,log_rows=spec['log_rows'][ti],width=width,packing=packing,
                row_point=point,lanes=branch_lanes(block,offset,width,packing,input_weights)))
    return result
