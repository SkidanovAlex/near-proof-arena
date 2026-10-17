"""Conditional shift vector-batching plus adaptive-round budget."""
import json
from pathlib import Path
import pq384_global_bus as bus


def main():
    root=Path(__file__).resolve().parents[2]
    fixture=root/'results/pq384-code-table-long193'
    spec=json.loads((fixture/'statement.json').read_text())['spec']
    tables=[]
    for t,table in enumerate(spec['air']['tables']):
        rounds=spec['log_rows'][t]
        auxiliary=bus.aux.layout(table)['aux_columns']
        profiles=[]
        for coordinates in (4,8):
            width=table['width']+coordinates*auxiliary
            profiles.append(dict(coordinates_per_auxiliary=coordinates,width=width,
                                 batching_numerator=2*width-1,rounds_numerator=2*rounds,
                                 composed_numerator=2*width-1+2*rounds,
                                 executable_profile=coordinates==4))
        tables.append(dict(table=t,source_width=table['width'],auxiliary_columns=auxiliary,
                           rounds=rounds,profiles=profiles))
    result=dict(status='CONDITIONAL_COMPONENT_BOUND',theorem='NearCompression.shift_wrong_vector_count',
                formula='(2*width-1+2*row_log)/field_size',tables=tables,
                premises=['Fixed original trace, target point and incorrect vector before batching alpha',
                          'Exact vector width and checked adaptive quadratic rounds',
                          'Terminal equality to actual original-column trace evaluations',
                          'Independent ideal challenge samples'],
                exclusions=['PCS authentication and common-trace extraction','Global transcript and quantum security',
                            'Ext8 profile is arithmetic projection; executable migration is not implemented'])
    (fixture/'shift-composed-budget.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
