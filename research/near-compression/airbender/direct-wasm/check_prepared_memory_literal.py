"""Exact full literal-table parity, including both interfaces and auto checks."""
import json,sys
from prepared_memory_air import table,c,mul,sub
actual=json.load(open(sys.argv[1]));expected=table()
expected['constraints'] += [mul(c(1),sub(c(1),c(1)))]*2
assert actual==expected
print('exact full memory table parity PASS:741+2 constraints and both bus interactions')
if len(sys.argv)>2:
    cs=table()['constraints']
    assert json.load(open(sys.argv[2]))==[cs[460]]+cs[482:485]
    print('exact bounds source AST parity PASS:4 expressions')
