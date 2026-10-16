"""Separate certified-layout Ext8 arithmetic adapter, not a PCS profile.
Flat coefficient order matches ZkFormal.Algebra.Fp8, x^8=11.
Base-field sources/twiddles remain scalar; challenges/folds have8coordinates.
"""
P=2013265921
ZERO=(0,)*8
ONE=(1,)+(0,)*7

def canonical(a):
    if not isinstance(a,(list,tuple)) or len(a)!=8 or any(type(x)is not int or not 0<=x<P for x in a):
        raise ValueError('canonical Ext8')
    return tuple(a)
def base(x):
    if type(x)is not int or not 0<=x<P:raise ValueError('canonical base')
    return (x,)+(0,)*7
def add(a,b):return tuple((x+y)%P for x,y in zip(a,b))
def sub(a,b):return tuple((x-y)%P for x,y in zip(a,b))
def scale(a,s):return tuple(x*s%P for x in a)
def mul(a,b):
    out=[0]*8
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[(i+j)%8]=(out[(i+j)%8]+x*y*(11 if i+j>=8 else 1))%P
    return tuple(out)
def power(a,n):
    if type(n)is not int or n<0:raise ValueError('exponent')
    out=ONE
    while n:
        if n&1:out=mul(out,a)
        a=mul(a,a);n//=2
    return out
def inv(a):return power(a,P**8-2)
def evaluate(coeff,x):
    out=ZERO
    for a in reversed(coeff):out=add(mul(out,x),a)
    return out
def fft(coeff,omega):
    n=len(coeff)
    if not n or n&(n-1) or (P-1)%n or pow(omega,n,P)!=1 or (n>1 and pow(omega,n//2,P)==1):
        raise ValueError('FFT domain')
    out=[canonical(a) for a in coeff];j=0
    for i in range(1,n):
        bit=n>>1
        while j&bit:j^=bit;bit>>=1
        j^=bit
        if i<j:out[i],out[j]=out[j],out[i]
    size=2
    while size<=n:
        step=pow(omega,n//size,P)
        for i in range(0,n,size):
            w=1
            for j in range(size//2):
                a=out[i+j];b=scale(out[i+j+size//2],w)
                out[i+j]=add(a,b);out[i+j+size//2]=sub(a,b);w=w*step%P
        size*=2
    return out
def affine_fold(coeff,r):
    r=canonical(r)
    if len(coeff)%2:raise ValueError('fold shape')
    return [add(coeff[i],mul(r,sub(coeff[i+1],coeff[i]))) for i in range(0,len(coeff),2)]
def quadratic(coeff,weights):
    if len(coeff)!=len(weights) or len(coeff)%2:raise ValueError('quadratic shape')
    q=[ZERO,ZERO,ZERO]
    for i in range(0,len(coeff),2):
        a,b=coeff[i:i+2];u,v=weights[i:i+2];d=sub(b,a);e=sub(v,u)
        q[0]=add(q[0],mul(a,u));q[1]=add(q[1],add(mul(d,u),mul(a,e)));q[2]=add(q[2],mul(d,e))
    return q
