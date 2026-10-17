#!/usr/bin/env python3
"""Two-stage canonical AIR bus experiment, fixed eight-row toy WHIR profile.

Original trace commitments precede bus challenges; auxiliary commitments/finals
precede all constraint challenges. No witness is an input to verification.
BLAKE2s/BabyBearExt4 experimental profile: NO quantum/security-level claim.
verify_local deliberately checks only local relations/openings, NOT bus balance.
"""
import copy
import hashlib
import itertools
import json
from pathlib import Path
import struct
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'generic-air'))
import bus_auxiliary as aux
from reference import schema,expr_degree,public_messages
from verify_whir_toy import P,ZERO,ONE,base,add,sub,mul,poly,ext,require,Transcript,_verify_with_handoff
from constraint_sumcheck import encode
from check_whir_handoff import mle
from table_constraint_whir import selectors,evaluate as eval_expr
import shift_opening as shift

BASIS=((1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1))


def constraints(table):
    # Exported allConstraints already has these; duplicate enforcement is harmless
    # and ensures omission of exporter-generated bit constraints is not a bypass.
    return table['constraints']+[['*',b,['+',b,['-',['c',1]]]]
                                for i in table['interactions'] for b in i['mult']]


def table_degree(table,num_pub):
    d=lambda e:expr_degree(e,table['width'],num_pub)
    degrees=[d(e) for e in constraints(table)]
    for i in table['interactions']:
        bits=[d(e) for e in i['mult']]
        m=max([d(e) for e in i['msg']],default=0)
        if len(bits)==0:degrees.append(2)
        elif len(bits)==1:degrees.append(bits[0]+m+2)
        else:
            degrees.extend([max(1,2*m),max(1,bits[0]+m+bits[1]+1),3])
            if len(bits)>2:degrees.extend([2]+[b+2 for b in bits[2:]])
    degree=max(degrees,default=0)
    require(degree<=16,'source/auxiliary degree exceeds experimental cap16')
    return degree


def validate(spec):
    air=spec['air'];schema(air)
    require(type(spec['log_rows']) is int and spec['log_rows']==3,'eight-row profile')
    require(isinstance(spec['public'],list) and all(type(v)is int and 0<=v<P for v in spec['public']),'public field')
    require(len(air['tables'])>0,'nonempty AIR')
    for table in air['tables']:
        require(table['width']>0 and table['maxLog']>=3,'table profile')
        require(aux.layout(table)['aux_columns']>0,'positive auxiliary width required')
    # Fit is a public deterministic precondition, checked before message expansion.
    public_messages(air,spec['public'])
    return [table_degree(t,air['numPub']) for t in air['tables']]


def check_roots(roots,count):
    require(isinstance(roots,list) and len(roots)==count,'root count')
    require(all(isinstance(r,list) and len(r)==8 and all(type(v)is int and 0<=v<2**32 for v in r)
                for r in roots),'root encoding')


def begin(spec,roots):
    degrees=validate(spec);tables=spec['air']['tables'];check_roots(roots,len(tables))
    digest=hashlib.sha256(json.dumps(spec,sort_keys=True,separators=(',',':')).encode()).digest()
    words=list(b'NEAR-GENERIC-AIR-BUS-WHIR-EXPERIMENT-V1')+list(struct.unpack('<8I',digest))
    words += [len(tables),8,4,1,1,2,1,1,8,8,4,0,0]
    for table,degree,root in zip(tables,degrees,roots):
        words += [table['width'],aux.layout(table)['aux_columns'],degree]+root
    t=Transcript(words)
    alpha=t.draw(1,True)[0];gamma=t.draw(1,True)[0]
    return words,t,alpha,gamma


def initialize_aux(t,tables,aux_roots,finals):
    check_roots(aux_roots,len(tables))
    require(isinstance(finals,list) and len(finals)==len(tables),'table final count')
    t.commit(list(b'ALL-AUXILIARY-COMMITMENTS-AND-FINALS-V1')+[len(tables)])
    for ti,(table,root,fs) in enumerate(zip(tables,aux_roots,finals)):
        require(isinstance(fs,list) and len(fs)==aux.layout(table)['finals'],'interaction final count')
        for v in fs:ext(v)
        t.commit([ti]+root+[len(fs)]);t.commit_ext(fs)


def flatten_aux_rows(table,rows):
    width=aux.layout(table)['aux_columns']
    require(isinstance(rows,list) and len(rows)==8 and all(isinstance(r,list) and len(r)==width
            and all(aux.canonical(v) for v in r) for r in rows),'auxiliary witness shape')
    return [[x for value in row for x in value] for row in rows]


def reconstruct(values):
    require(len(values)%4==0,'extension coordinate width')
    result=[]
    for k in range(0,len(values),4):
        value=ZERO
        for coordinate,basis in zip(values[k:k+4],BASIS):value=add(value,mul(coordinate,basis))
        result.append(value)
    return result


def weighted(spec,ti,alpha,gamma,finals,mixing,tau,point,current,nxt):
    table=spec['air']['tables'][ti];width=table['width'];sels=selectors(point)
    original=current[:width];original_next=nxt[:width]
    residuals=[eval_expr(e,original,original_next,spec['public'],sels) for e in constraints(table)]
    residuals+=aux.evaluate(table,original,original_next,spec['public'],sels,alpha,gamma,
                           reconstruct(current[width:]),reconstruct(nxt[width:]),finals)
    total=ZERO;power=ONE
    for residual in residuals:
        total=add(total,mul(power,residual));power=mul(power,mixing)
    return mul(shift.eq_point(tau,point),total)


def table_start(t,ti):
    t.commit(list(b'TABLE-CONSTRAINTS-V1')+[ti])
    return t.draw(1,True)[0],t.draw(3,True)


def opening_transcript(t,ti,branch):
    result=copy.copy(t)
    result.commit(list(b'TABLE-WHIR-OPENING-BRANCH-V1')+[ti,branch])
    return result


def prove(spec,roots,rows_by_table,aux_roots,aux_rows_by_table,finals_by_table):
    words,t,alpha,gamma=begin(spec,roots);tables=spec['air']['tables'];degrees=validate(spec)
    require(len(rows_by_table)==len(aux_rows_by_table)==len(finals_by_table)==len(tables),'witness table count')
    require(all(isinstance(fs,list) and all(aux.canonical(v) for v in fs) for fs in finals_by_table),'final field')
    finals=[[encode(v) for v in fs] for fs in finals_by_table]
    initialize_aux(t,tables,aux_roots,finals)
    partial={'aux_roots':copy.deepcopy(aux_roots),'finals':finals,'tables':[]};handoffs=[]
    for ti,(table,degree,source,auxiliary,fs) in enumerate(zip(tables,degrees,rows_by_table,aux_rows_by_table,finals_by_table)):
        require(isinstance(source,list) and len(source)==8 and all(isinstance(row,list) and len(row)==table['width']
                and all(type(v)is int and 0<=v<P for v in row) for row in source),'source witness shape')
        coordinates=flatten_aux_rows(table,auxiliary)
        rows=[a+b for a,b in zip(source,coordinates)];width=len(rows[0]);nxtrows=rows[1:]+rows[:1]
        mixing,tau=table_start(t,ti);point=[];rounds=[]
        for i in range(3):
            values=[]
            for node in range(degree+2):
                total=ZERO
                for suffix in itertools.product((ZERO,ONE),repeat=2-i):
                    at=point+[base(node)]+list(suffix)
                    current=[mle([r[c] for r in rows],at) for c in range(width)]
                    nxt=[mle([r[c] for r in nxtrows],at) for c in range(width)]
                    total=add(total,weighted(spec,ti,alpha,gamma,fs,mixing,tau,at,current,nxt))
                values.append(total)
            encoded=[encode(v) for v in shift.interpolate(values)];rounds.append(encoded)
            t.commit_ext(encoded);point.append(t.draw(1,True)[0])
        reduction,at,_=shift.prove(rows,point,t)
        partial['tables'].append({'constraint_rounds':rounds,'shift_reduction':reduction})
        branches=[]
        for branch,root in enumerate((roots[ti],aux_roots[ti])):
            fork=opening_transcript(t,ti,branch)
            branches.append({'root':root,'statement_words':words,
                             'pre_opening_seed':list(struct.unpack('<8I',fork.seed)),
                             'evaluation_point':[encode(v) for v in at]})
        handoffs.append(branches)
    return partial,handoffs


def verify_local(proof,spec,roots):
    """Check every local relation/PCS; intentionally does NOT check bus balance."""
    words,t,alpha,gamma=begin(spec,roots);tables=spec['air']['tables'];degrees=validate(spec)
    initialize_aux(t,tables,proof['aux_roots'],proof['finals'])
    require(isinstance(proof['tables'],list) and len(proof['tables'])==len(tables),'proof table count')
    for ti,(table,degree,part,fs) in enumerate(zip(tables,degrees,proof['tables'],proof['finals'])):
        mixing,tau=table_start(t,ti);point=[];claim=ZERO
        rounds=part['constraint_rounds'];require(len(rounds)==3,'constraint round count')
        for encoded in rounds:
            require(len(encoded)==degree+2,'constraint round degree');cs=[ext(v) for v in encoded]
            require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'bus table zerocheck identity')
            t.commit_ext(encoded);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r)
        source_width=table['width'];coordinate_width=4*aux.layout(table)['aux_columns'];width=source_width+coordinate_width
        reduction=part['shift_reduction']
        require(len(reduction['current_evals'])==len(reduction['next_evals'])==width,'terminal width')
        current=[ext(v) for v in reduction['current_evals']];nxt=[ext(v) for v in reduction['next_evals']]
        require(claim==weighted(spec,ti,alpha,gamma,[ext(v) for v in fs],mixing,tau,point,current,nxt),
                'bus terminal constraint')
        openings=part['openings'];require(isinstance(openings,list) and len(openings)==2,'two commitment openings')
        final=[]
        for opening,expected_width in zip(openings,(source_width,coordinate_width)):
            require(opening['statement_words']==words,'global statement binding')
            values=opening['proof']['witness_commitment']['evals']
            require(len(values)==expected_width,'opening coordinate width');final.extend(values)
        at=shift.verify(reduction,point,width,t,final)
        for branch,(opening,root,expected_width) in enumerate(zip(openings,(roots[ti],proof['aux_roots'][ti]),(source_width,coordinate_width))):
            fork=opening_transcript(t,ti,branch)
            _verify_with_handoff(opening,root,(fork,at),width=expected_width)
    return alpha,gamma


def global_balance(spec,finals,alpha,gamma):
    """Deterministic product equality, including exact public segment records.

    finals uses the encoded proof representation; this alone is not a proof.
    """
    tables=spec['air']['tables'];require(len(finals)==len(tables),'final table count')
    sends=ONE;receives=ONE
    for table,fs in zip(tables,finals):
        order=aux.layout(table)['order'];require(len(fs)==len(order),'final count')
        for index,value in zip(order,fs):
            if table['interactions'][index]['send']:sends=mul(sends,ext(value))
            else:receives=mul(receives,ext(value))
    for bus,send,message in public_messages(spec['air'],spec['public']):
        require(bus+1<P,'public bus tag')
        fingerprint=ZERO;power=ONE
        for value in message:
            fingerprint=add(fingerprint,mul(base(value),power));power=mul(power,alpha)
        fingerprint=add(fingerprint,mul(base(bus+1),power))
        factor=sub(gamma,fingerprint)
        if send:sends=mul(sends,factor)
        else:receives=mul(receives,factor)
    return sends==receives


def verify(proof,spec,roots):
    alpha,gamma=verify_local(proof,spec,roots)
    require(global_balance(spec,proof['finals'],alpha,gamma),'global bus product equality')
    return True
