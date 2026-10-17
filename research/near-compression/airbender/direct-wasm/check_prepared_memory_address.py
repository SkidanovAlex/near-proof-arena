"""Compare actual Lean-exported source expressions, with no AST normalization."""
import json,sys
from prepared_memory_air import table
actual=json.load(open(sys.argv[1]))
cs=table()['constraints']
assert actual==cs[:460]+cs[477:480]
print('exact address source AST parity PASS:463 expressions')
