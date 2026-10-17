"""Ext4 arbitrary-pair stack-kernel evaluation; no PCS authentication."""
import pq384_terminal_gkr as g
P=2013265921


def power(x,n):
    assert n >= 0
    out=g.ONE
    while n:
        if n&1:out=g.mul(out,x)
        x=g.mul(x,x);n//=2
    return out


def eq_uni(log,x,y):
    res=g.ONE
    for _ in range(log):
        res=g.add(g.mul(g.add(x,y),res),g.mul(g.sub(x,g.ONE),g.sub(y,g.ONE)))
        x=g.mul(x,x);y=g.mul(y,y)
    return g.mul(res,g.base(pow(1<<log,-1,P)))


def eq_cube(xs,ys):
    assert len(xs)==len(ys)
    out=g.ONE
    for x,y in zip(xs,ys):out=g.mul(out,g.add(g.mul(x,y),g.mul(g.sub(g.ONE,x),g.sub(g.ONE,y))))
    return out


def kernels(lskip,stack_log,height,start,r,u):
    assert 0<=lskip<=stack_log and 0<=height<=stack_log and len(u)==1+stack_log-lskip
    assert len(r)>=1+max(height-lskip,0)
    span=1<<max(height,lskip)
    assert start>=0 and start%span==0 and start+span<=1<<stack_log
    n=height-lskip;lift=max(n,0)
    bits=[g.base((start>>j)&1) for j in range(lskip+lift,stack_log)]
    high=eq_cube(u[1+lift:],bits)
    if n<0:
        local_log=height;rp=[power(r[0],1<<(-n))]
        indicator=eq_uni(-n,power(u[0],1<<height),g.ONE)
    else:local_log=lskip;rp=r[:1+lift];indicator=g.ONE
    up=u[:1+lift];eq=rot=g.ONE
    for x,y in reversed(list(zip(up[1:],rp[1:]))):
        rot=g.add(g.mul(g.mul(x,g.sub(g.ONE,y)),eq),g.mul(g.mul(g.sub(g.ONE,x),y),rot))
        eq=g.mul(eq,g.add(g.mul(x,y),g.mul(g.sub(g.ONE,x),g.sub(g.ONE,y))))
    omega=g.base(pow(31,(P-1)//(1<<local_log),P));shifted=g.mul(rp[0],omega)
    current=g.mul(eq_uni(local_log,up[0],rp[0]),eq)
    nxt=g.add(g.mul(eq_uni(local_log,up[0],shifted),eq),g.mul(g.mul(eq_uni(local_log,up[0],g.ONE),eq_uni(local_log,shifted,g.ONE)),g.sub(rot,eq)))
    scale=g.mul(high,indicator)
    return g.mul(scale,current),g.mul(scale,nxt)
