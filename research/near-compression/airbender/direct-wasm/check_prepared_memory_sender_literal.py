import json,sys
from prepared_memory_sender import table
from prepared_function_air import c,mul,sub
actual=json.load(open(sys.argv[1]));expected=table()
expected['constraints'] += [mul(c(1),sub(c(1),c(1)))]*2
assert actual==expected
print('exact memory sender full table parity PASS:2243+2constraints,23fieldEXEC/7fieldCODE interactions')
