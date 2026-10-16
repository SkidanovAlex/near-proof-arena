"""Independent typed-value AIR replay against real prepared Wasm traces.

Uses exported Lean constraints verbatim. Full typed EXEC/CODE/bus integration
is not implemented here. Exact trace transitions are checked independently.
"""
import argparse,copy,json
from pathlib import Path
P=2013265921
MASK=(1<<64)-1

def ev(e,row):
    op=e[0]
    if op=='c':return e[1]%P
    if op=='v':assert e[2]==0;return row[e[1]]
    if op=='+':return (ev(e[1],row)+ev(e[2],row))%P
    if op=='*':return ev(e[1],row)*ev(e[2],row)%P
    if op=='-':return -ev(e[1],row)%P
    raise AssertionError(op)
def accepted(cs,row):return all(ev(e,row)==0 for e in cs)
def putbits(row,base,n):row[base:base+16]=[(n>>i)&1 for i in range(16)]
def typed(tag,n):
    assert tag in (0,1) and 0<=n<(1<<(32 if tag==0 else 64))
    return dict(tag=tag,limbs=[(n>>(16*i))&65535 for i in range(4)])
def value(x):
    assert x['tag'] in (0,1) and len(x['limbs'])==4
    assert all(type(v) is int and 0<=v<65536 for v in x['limbs'])
    n=sum(v<<(16*i) for i,v in enumerate(x['limbs']))
    assert n<(1<<(32 if x['tag']==0 else 64))
    return n

def eqz_row(tag,n):
    row=[0]*80;row[:4]=typed(tag,n)['limbs'];row[12]=tag;row[13]=int(n==0)
    q=sum(row[:4]);row[14]=pow(q,P-2,P) if q else 0
    for i in range(4):putbits(row,16+16*i,row[i])
    return row

def add_row(a,b):
    row=[0]*208
    for base,n in [(0,a),(4,b),(8,(a+b)&MASK)]:row[base:base+4]=typed(1,n)['limbs']
    carry=0
    for i in range(4):carry=(row[i]+row[4+i]+carry)>>16;row[12+i]=carry
    for i in range(12):putbits(row,16+16*i,row[i])
    return row

def replay(case,eqz,add):
    previous=case['entry_after'];gadgets=0
    local_types=case['local_types']
    assert [x['tag'] for x in previous['frames'][0]['locals']]==local_types
    assert all(value(x)==0 for x in previous['frames'][0]['locals'])
    for event in case['exec_rows']:
        before=event['before'];after=event['after'];assert before==previous
        f=before['frames'][0];pc=f['pc'];desc=case['code'][pc]
        assert event['instruction']==desc['instruction'] and event['charge']==desc['charge']
        op=event['instruction']['opcode'];imm=event['instruction']['immediate']
        fee=0 if desc['charge'] is None else desc['charge']['constant']
        assert desc['charge'] is None or desc['charge']['linear']==0
        assert before['gas']['g']>=fee, 'This first fixture batch has no exhaustion'
        expected=copy.deepcopy(before);expected['gas']['g']-=fee
        st=expected['stack'];fr=expected['frames'][0];fr['pc']+=1;loc=fr['locals']
        for x in st+loc:
            n=value(x);assert accepted(eqz,eqz_row(x['tag'],n));gadgets+=1
        if op in (65,66):st.append(typed(int(op==66),imm))
        elif op in (106,124):
            tag=int(op==124);b=st.pop();a=st.pop();assert a['tag']==b['tag']==tag
            n=(value(a)+value(b))% (1<<(64 if tag else 32));st.append(typed(tag,n))
            if tag:assert accepted(add,add_row(value(a),value(b)));gadgets+=1
        elif op==80:
            a=st.pop();assert a['tag']==1
            row=eqz_row(1,value(a));assert accepted(eqz,row);gadgets+=1
            st.append(typed(0,row[13]))
        elif op==26:st.pop()
        elif op==32:st.append(copy.deepcopy(loc[imm]))
        elif op in (33,34):
            a=st[-1];assert a['tag']==local_types[imm];loc[imm]=copy.deepcopy(a)
            if op==33:st.pop()
        elif op==2:
            fr['labels'].insert(0,[desc['end_target'],0,len(st),0])
        elif op==13:
            a=st.pop();assert a['tag']==0
            if value(a)!=0:
                lab=fr['labels'].pop(0);assert lab[1]==lab[3]==0
                del st[lab[2]:];fr['pc']=lab[0]
        elif op==11:
            lab=fr['labels'].pop(0)
            if not fr['labels']:
                assert not st
                expected['frames'].pop(0);expected['stack_remaining']+=case['stack_charge']
        else:raise AssertionError(op)
        assert expected==after,(case['label'],pc,op,'state mismatch')
        previous=after
    return gadgets

def main():
    p=argparse.ArgumentParser();p.add_argument('--fixture',required=True);p.add_argument('--air',required=True);p.add_argument('--out',required=True);args=p.parse_args()
    fixture=json.load(open(args.fixture));air=json.load(open(args.air));eqz=air['eqz']['tables'][0]['constraints'];add=air['add64']['tables'][0]['constraints']
    assert len(eqz)==74 and len(add)==212
    values=[0,1,65535,65536,P,2*P,1<<32,(1<<63),MASK]
    rejected=0
    for n in values:
        row=eqz_row(1,n);assert accepted(eqz,row)
        for col in list(range(4))+[12,13]+list(range(16,80)):
            bad=row.copy();bad[col]=(bad[col]+1)%P;assert not accepted(eqz,bad);rejected+=1
        if n>=1<<32:
            bad=row.copy();bad[12]=0;assert not accepted(eqz,bad);rejected+=1
        bad=row.copy();bad[13]=1-row[13];assert not accepted(eqz,bad);rejected+=1
    pairs=[(0,0),(MASK,1),(MASK,MASK),(65535,1),(1<<63,1<<63),(P,P)]
    for a,b in pairs:
        row=add_row(a,b);assert accepted(add,row)
        for col in range(208):
            bad=row.copy();bad[col]=(bad[col]+1)%P;assert not accepted(add,bad);rejected+=1
    gadgets=sum(replay(case,eqz,add) for case in fixture['cases'])
    # Type-confusion checks: i64 local receives i32; eqz falsely leaves i64.
    semantic_rejects=0
    for case in fixture['cases']:
        for op in (33,34,80,124):
            target=next((i for i,e in enumerate(case['exec_rows']) if e['instruction']['opcode']==op),None)
            if target is None:continue
            bad=copy.deepcopy(case);e=bad['exec_rows'][target]
            if op==80:e['after']['stack'][-1]['tag']=1
            elif op==124:e['after']['stack'][-1]['tag']=0
            else:e['after']['frames'][0]['locals'][e['instruction']['immediate']]['tag']^=1
            try:replay(bad,eqz,add)
            except AssertionError:semantic_rejects+=1
            else:raise AssertionError('accepted type-confusion mutation')
    result=dict(status='PASS',actual_prepare_run_call_cases=len(fixture['cases']),source_constraint_counts=[len(eqz),len(add)],honest_value_cases=len(values),honest_add_cases=len(pairs),constraint_mutations_rejected=rejected,actual_trace_gadgets=gadgets,type_transition_mutations_rejected=semantic_rejects,scope='Isolated source AIR plus independent typed trace replay; full typed EXEC and CODE bus refinement pending')
    Path(args.out).write_text(json.dumps(result,indent=2));print(json.dumps(result))
if __name__=='__main__':main()
