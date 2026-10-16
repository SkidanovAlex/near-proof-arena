"""Trusted descriptor families for the weighted PCS input functional.
A pooled branch has one committed bank and a sum of logical projection terms.
The descriptor schema selects a distinct transcript domain; proofs cannot
select this family. Execution/GKR-to-bank mapping remains the caller's duty.
"""
import pq384_ext8_reference as f
from pq384_primitives import require
import pq384_ext8_input_weights as legacy
import ext8_pooled_weights as pool
POOLED_PROFILE='near-pq384-ext8-pooled-weighted-diagnostic-v1'
BASE_FIELDS={'root','log_rows','width','packing'}


def profile(branches,legacy_profile):
    return POOLED_PROFILE if any('terms' in b for b in branches) else legacy_profile


def lane_count(branch):return (branch['width']+branch['packing']-1)//branch['packing']


def validate_fields(branch):
    require(type(branch)is dict and (set(branch)==BASE_FIELDS|{'row_point','lanes'} or
                                    set(branch)==BASE_FIELDS|{'terms'}),'branch fields')


def validate_weights(branch):
    n,width,packing=branch['log_rows'],branch['width'],branch['packing']
    require(lane_count(branch)<=64,'lanes')
    if 'terms' in branch:
        terms=branch['terms'];require(type(terms)is list and 1<=len(terms)<=128,'pooled term count')
        for term in terms:
            require(type(term)is dict,'pooled term')
            pool.validate_term(term,n,width)
        return
    require(len(branch['row_point'])==n,'branch degree/point')
    for value in branch['row_point']:f.canonical(value)
    require(len(branch['lanes'])==lane_count(branch),'lanes')
    for j,pair in enumerate(branch['lanes']):
        require(len(pair)==2 and all(len(side)==packing for side in pair),'lane shape')
        for side in pair:
            for c,x in enumerate(side):
                value=f.canonical(x)
                if j*packing+c>=width:require(value==f.ZERO,'padding weight')


def lane_weights(branch,j,native):
    if 'terms' not in branch:
        a,b=branch['lanes'][j]
        return native.lane_weights(branch['row_point'],a,b) if hasattr(native,'lane_weights') else legacy.lane_weights(branch['row_point'],a,b)
    n,width,packing=branch['log_rows'],branch['width'],branch['packing'];result=None
    for term in branch['terms']:
        a,b=pool.column_lane(term,j*packing,packing)
        if all(x==f.ZERO for x in a+b):continue
        a,b=legacy.upper_zeta(a),legacy.upper_zeta(b);r,s=pool.masked_row_weights(term['row_point'],n)
        part=(native.tensor_weights(a,b,r,s) if hasattr(native,'tensor_weights') else
              [f.add(f.mul(x,y),f.mul(z,t)) for x,z in zip(a,b) for y,t in zip(r,s)])
        result=part if result is None else [f.add(x,y) for x,y in zip(result,part)]
    return result if result is not None else [f.ZERO]*((1<<n)*packing)


def lane_beta(branch,j,u):
    if 'terms' in branch:
        return pool.lane_weight_mle(branch['terms'],branch['log_rows'],branch['width'],j*branch['packing'],branch['packing'],u)
    a,b=branch['lanes'][j]
    return legacy.lane_weight_mle(branch['row_point'],a,b,u)
