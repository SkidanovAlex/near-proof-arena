"""SHA384 packed-column claim reduction; produces an UNDISCHARGED PCS obligation.

Diagnostic BabyBear Ext4 (v^4=11), not a selected PQ security field. The caller
must authenticate every returned lane evaluation at the returned packed point
against the SAME expected root. A handoff alone never verifies a proof.
"""
import struct
from pq384_primitives import P, Transcript, require, u64
from check_whir_handoff import add, sub, mul

ZERO=(0,0,0,0)


def canonical_ext(value):
    require(isinstance(value,(list,tuple)) and len(value)==4 and
            all(type(v)is int and 0<=v<P for v in value), 'canonical Ext4')
    return tuple(value)


def vector_bytes(values):
    return u64(len(values))+b''.join(struct.pack('<4I',*canonical_ext(v)) for v in values)


def mle_ext(values, point):
    values=[canonical_ext(v) for v in values]
    point=[canonical_ext(v) for v in point]
    require(len(values)==1<<len(point),'MLE dimension')
    for r in point:
        values=[add(a,mul(r,sub(b,a))) for a,b in zip(values[::2],values[1::2])]
    return values[0]


def packing_context(log_rows,width,packing):
    require(type(log_rows)is int and 1<=log_rows<=25,'row dimension')
    require(type(width)is int and 0<width<=1<<20,'source width')
    require(type(packing)is int and 0<packing<=1<<20 and packing&(packing-1)==0,
            'packing factor')
    n=1<<log_rows;size=4*n*packing
    require(size<=1<<27,'BabyBear domain capacity')
    omega=pow(440564289,(1<<27)//size,P);lanes=(width+packing-1)//packing
    return (b'NEAR-PQ384-RS-PACKED-V2/row-low-column-high-mobius/'
            b'consecutive-column-groups/zero-pad-columns-and-lde4/'
            b'natural-domain/lane-major-pairs/le-u32'
            +b''.join(u64(v) for v in (P,n,width,packing,lanes,size,omega)))


def derive_handoff(statement, parent_binding, expected_root, log_rows, width,
                   packing, row_point, column_claims):
    """All inputs come from the enclosing verifier, not proof-selected metadata.

    parent_binding must encode the enclosing transcript branch. This standalone
    function does not establish that it is linked to an AIR proof transcript.
    """
    require(type(statement)is bytes and type(parent_binding)is bytes,'statement/parent bytes')
    require(type(expected_root)is bytes and len(expected_root)==48,'expected SHA384 root')
    ctx=packing_context(log_rows,width,packing)
    require(isinstance(row_point,(list,tuple)) and len(row_point)==log_rows,'row point shape')
    require(isinstance(column_claims,(list,tuple)) and len(column_claims)==width,'column claims shape')
    point=[canonical_ext(v) for v in row_point]
    claims=[canonical_ext(v) for v in column_claims]
    transcript=Transcript(b'NEAR-PACKED-CLAIM-HANDOFF-V1/Ext4-v4=11')
    transcript.commit(b'statement',statement)
    transcript.commit(b'parent-branch',parent_binding)
    transcript.commit(b'packing-context',ctx)
    transcript.commit(b'source-root',expected_root)
    transcript.commit(b'row-point',vector_bytes(point))
    # Bind the entire vector before obtaining any column coordinates.
    transcript.commit(b'column-claims',vector_bytes(claims))
    p=packing.bit_length()-1
    if p:
        challenge,_=transcript.draw(b'column-point',p,4)
        challenge=[tuple(v) for v in challenge]
    else:challenge=[]
    lanes=[]
    for start in range(0,width,packing):
        group=claims[start:start+packing]
        lanes.append(mle_ext(group+[ZERO]*(packing-len(group)),challenge))
    transcript.commit(b'packed-lane-claims',vector_bytes(lanes))
    return {'kind':'undischarged-packed-pcs-obligation',
            'context_hex':ctx.hex(),'expected_root_hex':expected_root.hex(),
            'packed_point':[list(v) for v in point+challenge],
            'lane_claims':[list(v) for v in lanes],
            'transcript_seed_hex':transcript.seed.hex()}
