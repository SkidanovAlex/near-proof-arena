"""Code-switch algebra only: grouped source queries and functional injection.
No transcript, commitment extraction, proximity or security profile is defined.
A caller must fix the new commitment and answers before drawing mix scalars.
"""
import pq384_ext8_reference as f
from pq384_primitives import require


def fold_coset(values,point,root,challenges):
    """Values are f(point*root**j), j=0..2**k-1 in natural order.
    Returns the k-fold coefficient polynomial at point**(2**k).
    Pair antipodes before squaring; adjacent-value folding is incorrect.
    """
    values=[f.canonical(v) for v in values];challenges=[f.canonical(r) for r in challenges]
    n=1<<len(challenges)
    require(len(values)==n,'coset shape')
    require(type(point)is int and 0<point<f.P and type(root)is int and 0<root<f.P,'coset points')
    require(pow(root,n,f.P)==1 and (n==1 or pow(root,n//2,f.P)!=1),'primitive coset root')
    for r in challenges:
        half=len(values)//2;out=[];x=point
        for j in range(half):
            even=f.scale(f.add(values[j],values[j+half]),pow(2,-1,f.P))
            odd=f.scale(f.sub(values[j],values[j+half]),pow(2*x,-1,f.P))
            out.append(f.add(even,f.mul(r,f.sub(odd,even))))
            x=x*root%f.P
        values=out;point=point*point%f.P;root=root*root%f.P
    return values[0]


def inject(weights,claim,points,answers,mixers):
    """new residual = old residual + sum mixer*(polynomial(point)-answer).
    The power weights are monomial evaluation weights, not Boolean eq weights.
    """
    weights=[f.canonical(x) for x in weights];claim=f.canonical(claim)
    require(len(weights)>0 and len(points)==len(answers)==len(mixers),'injection shape')
    for point,answer,mixer in zip(points,answers,mixers):
        point,answer,mixer=map(f.canonical,(point,answer,mixer));power=f.ONE
        for i in range(len(weights)):
            weights[i]=f.add(weights[i],f.mul(mixer,power));power=f.mul(power,point)
        claim=f.add(claim,f.mul(mixer,answer))
    return weights,claim


def dot(coefficients,weights):
    require(len(coefficients)==len(weights),'functional shape')
    result=f.ZERO
    for c,w in zip(coefficients,weights):result=f.add(result,f.mul(f.canonical(c),f.canonical(w)))
    return result
