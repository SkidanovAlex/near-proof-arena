"""Actual prepared-step sender/adapter attachment and coherent forgery tests."""
import json,sys
import prepared_memory_sender as ex
import prepared_memory_air as mem
from prepared_function_air import putbits,eval_expr
case=json.load(open(sys.argv[1]));assert case['actual_run_call']
events=case['rows'];assert len(events)==4
rows=[ex.witness(e,3) for e in events]
errors=[(r,i,x) for r,res in enumerate(ex.residuals(rows)) for i,x in enumerate(res) if x]
assert not errors,errors[:8]
access=[mem.witness(e['opcode'],e['address'],e['offset'],e['pages'],e['value'],e['raw'],e['clock'],3) for e in events]
for r,(sender,adapter) in enumerate(zip(rows,access)):
  assert not any(mem.residuals(adapter))
  assert ex.message(sender)==mem.messages(adapter)[0] and len(ex.message(sender))==23
  actual=events[r]['next_stack']
  if r+1<len(rows):assert actual==events[r+1]['stack']
  code=[eval_expr(e,sender,sender,[],False,False) for e in ex.table()['interactions'][1]['msg']]
  assert code==[3,0,events[r]['pc'],0,events[r]['opcode'],events[r]['offset']&65535,events[r]['offset']>>16]
# Coherent adapter replacements pass adapter local AIR but fail exact EXEC bus.
bus_bad=0
for i,e in enumerate(events):
  for change in ['address','offset','clock','instance','value_or_raw']:
    a=dict(e);instance=3
    if change=='instance':instance=4
    elif change=='value_or_raw':
      if e['opcode']>=0x36:a['value']^=1
      else:a['raw']^=1
    else:a[change]+=1
    forged=mem.witness(a['opcode'],a['address'],a['offset'],a['pages'],a['value'],a['raw'],a['clock'],instance)
    assert not any(mem.residuals(forged))
    assert ex.message(rows[i])!=mem.messages(forged)[0]
    bus_bad+=1
# Repaired Boolean rows still must satisfy complete stack/clock/PC transitions.
transition_bad=0
for i in range(1,4):
  for col in [0,ex.TYPE,ex.SP,ex.CLOCK,ex.PC,ex.PAGES,ex.INSTANCE]:
    bad=[r.copy() for r in rows];bad[i][col]^=1
    assert any(any(x) for x in ex.residuals(bad));transition_bad+=1
# Type/address-depth source checks.
for row_idx,col in [(0,ex.TYPE+3),(1,ex.TYPE+2),(1,ex.TYPE+3)]:
  bad=[r.copy() for r in rows];bad[row_idx][col]^=1
  assert any(any(x) for x in ex.residuals(bad));transition_bad+=1
print(json.dumps(dict(profile='memory-exec-sender-v1',columns=ex.WIDTH,constraints=len(ex.table()['constraints']),
  actual_prepared_steps=4,actual_run_call=True,matched_exec_fields=23,coherent_bus_forgeries=bus_bad,
  source_forgeries=transition_bad,scope='stack8 contiguous memory segment; CODE receiver, boundary and gas authentication still open')))
