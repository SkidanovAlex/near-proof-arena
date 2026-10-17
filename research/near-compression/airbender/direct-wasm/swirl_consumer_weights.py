"""Exact terminal batch-constraint scalar as node weights and a constant.

Caller supplies traces in verifier order and authenticated transcript-derived
controls. This module neither derives those controls nor proves PCS binding.
"""
import pq384_terminal_gkr as g


def powers(x,n):
    out=[];cur=g.ONE
    for _ in range(n):out.append(cur);cur=g.mul(cur,x)
    return out


def terminal_weights(records, *, lam, beta, mu, eq_ns, eq_sharp, norms, eq3bs):
    count=len(records)
    if not all(len(x)==count for x in (eq_ns,eq_sharp,norms,eq3bs)):
        raise ValueError('trace/control shape')
    mus=powers(mu,3*count)
    weights=[];constant=g.ZERO
    for t,record in enumerate(records):
        n=len(record['nodes']);w=[g.ZERO]*n
        interactions=record['interactions']
        if len(eq3bs[t])!=len(interactions):raise ValueError('interaction/equality shape')
        def accumulate(index,value):
            if type(index) is not int or not 0<=index<n:raise ValueError('node index')
            w[index]=g.add(w[index],value)
        for lp,index in zip(powers(lam,len(record['constraints'])),record['constraints']):
            accumulate(index,g.mul(g.mul(mus[2*count+t],eq_ns[t]),lp))
        for equality,interaction in zip(eq3bs[t],interactions):
            common=g.mul(eq_sharp[t],equality)
            accumulate(interaction['count'],g.mul(g.mul(mus[2*t],norms[t]),common))
            denom_scale=g.mul(mus[2*t+1],common)
            bps=powers(beta,len(interaction['message'])+1)
            for index,bp in zip(interaction['message'],bps):accumulate(index,g.mul(denom_scale,bp))
            bus=interaction['bus']
            if type(bus) is not int or not 0<=bus<2**16:raise ValueError('bus index')
            constant=g.add(constant,g.mul(g.mul(denom_scale,bps[-1]),g.base(bus+1)))
        weights.append(w)
    return weights,constant


def direct_terminal(records, values, *, lam, beta, mu, eq_ns, eq_sharp, norms, eq3bs):
    """Independent procedural transcription of the native output consumers."""
    interaction_outputs=[];constraint_outputs=[]
    for t,r in enumerate(records):
        nodes=values[t];expr=g.ZERO;lp=g.ONE
        for index in r['constraints']:
            expr=g.add(expr,g.mul(nodes[index],lp));lp=g.mul(lp,lam)
        constraint_outputs.append(g.mul(eq_ns[t],expr))
        num=g.ZERO;denom=g.ZERO
        for j,x in enumerate(r['interactions']):
            d=g.ZERO;bp=g.ONE
            for index in x['message']:
                d=g.add(d,g.mul(nodes[index],bp));bp=g.mul(bp,beta)
            d=g.add(d,g.mul(g.base(x['bus']+1),bp))
            num=g.add(num,g.mul(eq3bs[t][j],nodes[x['count']]))
            denom=g.add(denom,g.mul(eq3bs[t][j],d))
        interaction_outputs.extend([g.mul(g.mul(num,norms[t]),eq_sharp[t]),g.mul(denom,eq_sharp[t])])
    result=g.ZERO;mp=g.ONE
    for value in interaction_outputs+constraint_outputs:
        result=g.add(result,g.mul(mp,value));mp=g.mul(mp,mu)
    return result
