"""Complete small-table opening check for native packed SHA384 RS commitments.

Discloses every base-field monomial coefficient (not zero knowledge). This
discharges a packed-point PCS obligation exactly, conditional on hash binding.
The original column-vector reduction remains probabilistic; Ext4 is diagnostic.
Large instances fail closed rather than falling back to unchecked openings.
"""
from pq384_primitives import P, require, field_words, merkle_tree
from packed_claim_handoff import packing_context, derive_handoff, canonical_ext
from check_whir_handoff import add, mul


def shape(log_rows,width,packing):
    context=packing_context(log_rows,width,packing)
    degree=(1<<log_rows)*packing;lanes=(width+packing-1)//packing
    require(degree<=64 and lanes<=64,'small packed disclosure capacity')
    return context,degree,lanes


def prove_disclosure(rows,packing):
    require(isinstance(rows,list) and len(rows)>=2 and len(rows)&(len(rows)-1)==0,'source rows')
    require(isinstance(rows[0],list) and len(rows[0])>0,'source width')
    width=len(rows[0]);n=len(rows)
    require(all(isinstance(r,list) and len(r)==width and
                all(type(v)is int and 0<=v<P for v in r) for r in rows),'source fields')
    _,degree,lanes=shape(n.bit_length()-1,width,packing)
    coefficients=[]
    for lane in range(lanes):
        values=[rows[r][lane*packing+c] if lane*packing+c<width else 0
                for c in range(packing) for r in range(n)]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:values[i]=(values[i]-values[i^bit])%P
            bit*=2
        coefficients.append(values)
    return {'profile':'near-packed-disclosure-v1','coefficients':coefficients}


def scalar_eval(coefficients,x):
    result=0
    for c in reversed(coefficients):result=(result*x+c)%P
    return result


def tensor_eval(coefficients,point):
    values=[(v,0,0,0) for v in coefficients]
    require(len(values)==1<<len(point),'monomial tensor shape')
    for r in point:
        r=canonical_ext(r)
        # Coefficients are monomials, not Boolean evaluations.
        values=[add(a,mul(r,b)) for a,b in zip(values[::2],values[1::2])]
    return values[0]


def verify_disclosure(proof, *, statement, parent_binding, expected_root,
                      log_rows, width, packing, row_point, column_claims):
    context,degree,lanes=shape(log_rows,width,packing)
    require(type(proof)is dict and set(proof)=={'profile','coefficients'} and
            proof['profile']=='near-packed-disclosure-v1','packed disclosure fields')
    coefficients=proof['coefficients']
    require(isinstance(coefficients,list) and len(coefficients)==lanes and
            all(isinstance(cs,list) and len(cs)==degree and
                all(type(c)is int and 0<=c<P for c in cs) for cs in coefficients),
            'packed coefficients')
    handoff=derive_handoff(statement,parent_binding,expected_root,log_rows,width,
                           packing,row_point,column_claims)
    # Exact padding check on the disclosed polynomial's Boolean evaluations.
    for lane,cs in enumerate(coefficients):
        if (lane+1)*packing<=width:continue
        values=cs.copy();bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:values[i]=(values[i]+values[i^bit])%P
            bit*=2
        require(all(values[i]==0 for i in range(degree)
                    if lane*packing+(i>>log_rows)>=width),'nonzero padded column')
    size=degree*4;omega=pow(440564289,(1<<27)//size,P)
    leaves=[];x=1
    for _ in range(size//2):
        leaves.append(field_words([v for cs in coefficients
                                   for v in (scalar_eval(cs,x),scalar_eval(cs,(-x)%P))]))
        x=x*omega%P
    require(merkle_tree(leaves,context)[0]==expected_root,'packed oracle root mismatch')
    actual=[list(tensor_eval(cs,handoff['packed_point'])) for cs in coefficients]
    require(actual==handoff['lane_claims'],'packed opening claim mismatch')
    return True
