"""Conservative ideal-challenge bus budget for the retained literal slice.

Not a whole-protocol soundness estimate: source extraction, auxiliary/local
checks, transcript distribution, commitments and QROM are separate obligations.
"""
import json
import math
import subprocess
from pathlib import Path
from reference import public_messages
from prepared_code_table_air import air, P


def budget(spec):
    public = public_messages(spec['air'], spec['public'])
    public = list(public)
    support = len(public)
    width = max((len(m)+1 for _,_,m in public), default=0)
    masses = {True:0, False:0}
    for _, send, _ in public:
        masses[send] += 1
    tables = []
    for table, log_rows in zip(spec['air']['tables'], spec['log_rows']):
        rows = 1 << log_rows
        support += rows * len(table['interactions'])
        entry = dict(rows=rows, send_mass=0, receive_mass=0)
        for interaction in table['interactions']:
            width = max(width, len(interaction['msg'])+1)
            mass = rows * ((1 << len(interaction['mult']))-1)
            masses[interaction['send']] += mass
            entry['send_mass' if interaction['send'] else 'receive_mass'] += mass
        tables.append(entry)
    alpha = support * width
    gamma = max(masses.values())
    return dict(tables=tables, public_records=len(public), support_bound=support,
                tagged_padded_width=width, alpha_bad_count=alpha, gamma_bad_count=gamma,
                joint_error_numerator=alpha+gamma)


def main():
    package = Path(__file__).resolve().parents[2]
    fixture = package/'results/pq384-code-table-long193'
    spec = json.loads((fixture/'statement.json').read_text())['spec']
    assert spec['air'] == air(193)
    result = budget(spec)
    lean = subprocess.run(['lake','env','lean','--run','PreparedSliceBusBudget.lean',
                           str(fixture/'statement.json')],cwd=package,check=True,capture_output=True,text=True)
    actual = json.loads(lean.stdout)
    assert actual['support'] == result['support_bound']
    assert max(actual['send_mass'],actual['receive_mass']) == result['gamma_bad_count']
    assert actual['numerator'] == result['joint_error_numerator']
    result['literal_lean_budget'] = actual
    numerator = result['joint_error_numerator']
    result['ideal_uniform_field_bounds'] = [dict(extension_degree=d,
        field_size=P**d, numerator=numerator, denominator=P**d,
        bound_bits=math.log2(P**d)-math.log2(numerator)) for d in (4,8)]
    result['status'] = 'CONDITIONAL_COMPONENT_BOUND'
    result['theorem'] = 'NearCompression.bus_trace_budget_fp8_bound'
    result['conditions'] = [
        'Same fixed source trace/messages before alpha and gamma; commitment extraction not supplied',
        'Literal tags/widths, support and mass discharged in PreparedLiteralBusSoundness; local validity and authenticated extraction pending',
        'Auxiliary gates and final products correspond to expanded natural multiplicities',
        'Independent uniform field challenges; executable hash sampler and QROM not covered']
    result['interpretation'] = 'Upper error bound only, not an attack or lower bound on achievable security. Ext4 budget cannot certify 128 ideal bits via this bound; Ext8 budget alone does not certify quantum security.'
    (fixture/'bus-budget.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
