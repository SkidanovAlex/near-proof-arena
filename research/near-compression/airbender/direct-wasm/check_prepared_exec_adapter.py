"""Compare lowered old constraints with new EXEC ASTs using only zero/one rules."""
import json
import subprocess
import sys
from pathlib import Path
from prepared_code_table_air import exec_table, WIDTH, c, v, mul, sub


def simplify(e):
    tag = e[0]
    if tag in ('+', '*'):
        x, y = map(simplify, e[1:])
        if tag == '+':
            if x == ['c', 0]: return y
            if y == ['c', 0]: return x
        else:
            if x == ['c', 0] or y == ['c', 0]: return ['c', 0]
            if x == ['c', 1]: return y
            if y == ['c', 1]: return x
        return [tag, x, y]
    if tag == '-':
        x = simplify(e[1])
        return x if x == ['c', 0] else ['-', x]
    return e


root = Path(__file__).resolve().parents[2]
formal = json.loads(subprocess.check_output(
    ['lake', 'env', 'lean', '--run', 'PreparedExecAdapterExport.lean'], cwd=root))
original = exec_table()['constraints']
source = [simplify(e) for e in original]
def no_first(e):
    if e[0] == 'first': return False
    if e[0] in ('+', '*'): return no_first(e[1]) and no_first(e[2])
    if e[0] == '-': return no_first(e[1])
    return True
boolean_indices = []
for i in range(WIDTH):
    expected = sub(mul(v(i), sub(v(i), c(1))), c(0))
    assert expected in original, ('missing exact boolean constraint', i)
    boolean_indices.append(original.index(expected))
matches = [[i for i, e in enumerate(source) if e == simplify(f) and no_first(original[i])] for f in formal]
assert all(matches), [(i, f) for i, (f, m) in enumerate(zip(formal, matches)) if not m]
assert all(e in original for e in formal[-9:-1]), 'exact gas source membership'
assert formal[-1] in original, 'exact SP choice membership'
report = dict(exact_sp_choice=True, exact_gas_constraints=8, status='PASS', matched_expressions=len(formal), source_indices=matches,
              exact_boolean_constraints=len(boolean_indices), no_first_checked=True,
              normalization='Only recursive zero/one add/mul and negzero rewrites, as proved in prepared_exec_simplify_eval',
              scope='Local source AST adapters and numeric PC; no complete new EXEC refinement')
Path(sys.argv[1]).write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
