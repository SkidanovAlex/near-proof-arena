"""Independent coefficient claim by separable contraction, without a tensor.
Retains reference Mobius coefficient conversion and uses Python integer dot
products modulo P; no native prover arithmetic is used.
"""
import pq384_ext8_reference as f
import pq384_ext8_input_weights as w
from test_ext8_input_weights import coefficients


def coordinate_columns(weights):
    return tuple(zip(*weights))


def dot_base(coefficients, columns):
    assert len(columns)==8 and all(len(column)==len(coefficients) for column in columns)
    return tuple(sum(c*x for c,x in zip(coefficients,column))%f.P for column in columns)


def coefficient_claim(rows,branch):
    n=1<<branch['log_rows']
    assert len(rows)==n and all(len(r)==branch['width'] for r in rows)
    assert len(branch['row_point'])==branch['log_rows']
    assert len(branch['lanes'])==(branch['width']+branch['packing']-1)//branch['packing']
    r,s=w.row_weights(branch['row_point'])
    rcols,scols=coordinate_columns(r),coordinate_columns(s)
    value=f.ZERO
    for j,(current,nxt) in enumerate(branch['lanes']):
        cs=coefficients(rows,j*branch['packing'],branch['packing'])
        a,b=w.upper_zeta(current),w.upper_zeta(nxt)
        assert len(a)==len(b)==branch['packing'] and len(cs)==n*len(a)
        for k,(x,y) in enumerate(zip(a,b)):
            segment=cs[k*n:(k+1)*n]
            value=f.add(value,f.add(f.mul(x,dot_base(segment,rcols)),f.mul(y,dot_base(segment,scols))))
    return value
