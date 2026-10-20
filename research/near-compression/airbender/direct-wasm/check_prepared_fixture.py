"""Independent integer checks on exported semantic fixtures; this is not an AIR verifier."""
import json,sys
x=json.load(open(sys.argv[1]));assert not x['air_implemented']
for case in x['cases']:
    stack=[];previous=None
    for clock,row in enumerate(case['exec_rows']):
        assert row['clock']==clock and row['pc']==clock
        assert row['instruction']==case['code'][clock]['instruction']
        assert row['charge']==case['code'][clock]['charge']
        before,after=row['before'],row['after']
        if previous is not None:assert before==previous
        assert before['stack']==stack
        op=row['instruction']['opcode'];imm=row['instruction']['immediate']
        events=[]
        def event(slot,write,value):return dict(clock=clock,slot=slot,write=write,value=value)
        if row['status']=='abort':
            assert row['error'] is not None and before['stack']==after['stack']
            assert before['frames']==after['frames'] and not row['stack_events']
            assert row['charge']['constant']>before['gas']['g']
        else:
            if op==65:
                value=dict(tag=0,limbs=[imm%65536,imm//65536])
                events=[event(len(stack),True,value)];stack=stack+[value]
            elif op==106:
                n=len(stack);a,b=stack[-2:]
                v=(a['limbs'][0]+65536*a['limbs'][1]+b['limbs'][0]+65536*b['limbs'][1])%2**32
                result=dict(tag=0,limbs=[v%65536,v//65536])
                events=[event(n-1,False,b),event(n-2,False,a),event(n-2,True,result)]
                stack=stack[:-2]+[result]
            elif op==26:
                events=[event(len(stack)-1,False,stack[-1])];stack=stack[:-1]
            else:assert op==11 and not stack and row['status']=='finish'
            assert after['stack']==stack and row['stack_events']==events
            charge=0 if row['charge'] is None else row['charge']['constant']
            assert after['gas']['g']==before['gas']['g']-charge
        previous=after
    if case['label']=='range-charge-exhaustion':assert len(case['exec_rows'])==1 and case['error'] is not None
    else:assert len(case['exec_rows'])==5 and case['error'] is None
    # Crucially preparation charges the entire const/const/add/drop range at PC0.
    assert case['code'][0]['charge']['constant']==4*822756
    assert all(r['charge'] is None for r in case['code'][1:])
print('PASS: five real prepared fixtures; code, stack events, integer arithmetic, exact range gas and exhaustion')
