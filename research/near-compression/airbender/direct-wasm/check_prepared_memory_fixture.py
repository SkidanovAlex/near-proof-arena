"""Compare scalar AIR with actual Lean interpreter fixture; no mocked gas claim."""
import json,sys
from prepared_memory_air import *
cases=json.load(open(sys.argv[1]));assert len(cases)==76
for x in cases:
    row=witness(x['opcode'],x['address'],x['offset'],x['pages'],x['value'],x['raw'],clock=91,instance=3)
    assert not any(residuals(row)),x
    decode=lambda base,n:sum(row[base+i]<<i for i in range(n))
    assert decode(RAW,64)==x['raw'] and decode(RESULT,64)==x['result'],x
    spec=next(o for o in OPS if o[0]==x['opcode'])
    assert spec[1]==x['width'] and (spec[4] or spec[3]==x['tag'])
    mem=messages(row)[1]
    assert mem[:6]==[3,0,91,0,0,0]
    assert mem[6:9]==[((x['address']+x['offset'])>>(16*i))&65535 for i in range(3)]
    assert mem[9:11]==[x['width'],spec[4]]
    limbs=lambda value,bits:[(value>>i)&65535 for i in range(0,bits,16)]
    assert mem[11:]==limbs(x['raw'],64)
    expected_exec=[3,0,91,0,0,0,x['opcode'],spec[3],spec[4]]
    expected_exec+=limbs(x['address'],32)+limbs(x['offset'],32)+limbs(x['pages'],17)
    expected_exec+=limbs(x['value'],64)+limbs(x['result'],64)
    assert messages(row)[0]==expected_exec and len(expected_exec)==23
print('actual Wasm exec vs scalar AIR PASS:76 load/store cases, both-page boundaries, typed values, prefix/PC and memory byte checks')
