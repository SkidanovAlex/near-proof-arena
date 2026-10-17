"""Experimental phase-separated bank projections and coefficient weights.
A logical table occupies its first 2**n rows and a fixed column interval.
Unused bank cells are unrestricted. Next-row rotation wraps at the LOGICAL
height, not the bank height. The PCS weight-family adapter is separate from execution commitment mapping.
"""
import pq384_ext8_reference as f
import pq384_ext8_input_weights as w
from pq384_primitives import require
from test_ext8_input_weights import coefficients
from ext8_coefficient_claim_contract import coordinate_columns,dot_base


def phase_layout(spec,use_table=3):
    import pq384_ext8_auxiliary as bus_auxiliary
    count=len(spec['air']['tables']);require(type(use_table)is int and 0<=use_table<count,'use table')
    groups=[('source',[(i,spec['air']['tables'][i]['width']) for i in range(count) if i!=use_table]),
            ('auxiliary',[(i,8*bus_auxiliary.layout(t)['aux_columns']) for i,t in enumerate(spec['air']['tables'])]),
            ('source',[(use_table,spec['air']['tables'][use_table]['width'])])]
    banks=[]
    for phase,members in groups:
        members=[(i,width) for i,width in members if width]
        if not members:continue
        offset=0;blocks=[]
        for i,width in members:
            blocks.append(dict(table=i,log_rows=spec['log_rows'][i],width=width,offset=offset));offset+=width
        banks.append(dict(phase=phase,log_rows=max(x['log_rows'] for x in blocks),width=offset,blocks=blocks))
    return banks


def validate_term(term,bank_log,bank_width):
    require(set(term)=={'offset','width','row_point','current','next'},'term fields')
    offset,width=term['offset'],term['width']
    require(type(offset)is int and type(width)is int and 0<=offset and 0<width and offset+width<=bank_width,'column interval')
    require(0<=len(term['row_point'])<=bank_log,'logical height')
    require(len(term['current'])==len(term['next'])==width,'column weights')
    for values in (term['row_point'],term['current'],term['next']):
        for value in values:f.canonical(value)


def masked_row_weights(point,bank_log):
    require(len(point)<=bank_log,'logical height')
    equality=w.eqs(point);shift=[equality[(i-1)%len(equality)] for i in range(len(equality))]
    zero=[f.ZERO]*((1<<bank_log)-len(equality))
    return w.upper_zeta(equality+zero),w.upper_zeta(shift+zero)


def column_lane(term,start,packing):
    def side(name):
        return [f.canonical(term[name][c-term['offset']]) if term['offset']<=c<term['offset']+term['width'] else f.ZERO
                for c in range(start,start+packing)]
    return side('current'),side('next')


def lane_weights(terms,bank_log,bank_width,start,packing):
    require(type(packing)is int and packing>0 and packing&(packing-1)==0,'packing')
    result=[f.ZERO]*((1<<bank_log)*packing)
    for term in terms:
        validate_term(term,bank_log,bank_width)
        current,nxt=column_lane(term,start,packing)
        a,b=w.upper_zeta(current),w.upper_zeta(nxt);r,s=masked_row_weights(term['row_point'],bank_log)
        result=[f.add(prior,f.add(f.mul(x,y),f.mul(z,t))) for prior,(x,z,y,t) in
                zip(result,((x,z,y,t) for x,z in zip(a,b) for y,t in zip(r,s)))]
    return result


def lane_weight_mle(terms,bank_log,bank_width,start,packing,u):
    require(type(packing)is int and packing>0 and packing&(packing-1)==0,'packing')
    require(len(u)==bank_log+packing.bit_length()-1,'MLE point')
    result=f.ZERO
    for term in terms:
        validate_term(term,bank_log,bank_width);n=len(term['row_point']);factor=f.ONE
        for x in u[n:bank_log]:factor=f.mul(factor,f.sub(f.ONE,f.canonical(x)))
        a,b=column_lane(term,start,packing)
        value=w.lane_weight_mle(term['row_point'],a,b,u[:n]+u[bank_log:])
        result=f.add(result,f.mul(factor,value))
    return result


def coefficient_claim(rows,terms,packing):
    n=len(rows);width=len(rows[0]);bank_log=n.bit_length()-1
    require(n>0 and n&(n-1)==0 and all(len(row)==width for row in rows),'bank shape')
    require(type(packing)is int and packing>0 and packing&(packing-1)==0,'packing')
    prepared=[]
    for term in terms:
        validate_term(term,bank_log,width)
        r,s=masked_row_weights(term['row_point'],bank_log)
        prepared.append((term,coordinate_columns(r),coordinate_columns(s)))
    result=f.ZERO
    for start in range(0,width,packing):
        cs=coefficients(rows,start,packing)
        for term,r,s in prepared:
            a,b=column_lane(term,start,packing);a,b=w.upper_zeta(a),w.upper_zeta(b)
            for k,(x,y) in enumerate(zip(a,b)):
                segment=cs[k*n:(k+1)*n]
                result=f.add(result,f.add(f.mul(x,dot_base(segment,r)),f.mul(y,dot_base(segment,s))))
    return result


def direct_claim(rows,terms):
    result=f.ZERO;bank_log=len(rows).bit_length()-1
    for term in terms:
        validate_term(term,bank_log,len(rows[0]));n=1<<len(term['row_point'])
        for r,weight in enumerate(w.eqs(term['row_point'])):
            for c,(a,b) in enumerate(zip(term['current'],term['next'])):
                col=term['offset']+c
                value=f.add(f.scale(a,rows[r][col]),f.scale(b,rows[(r+1)%n][col]))
                result=f.add(result,f.mul(weight,value))
    return result
