"""Retain reconstruction certificates after full fixed-profile proof verification."""
import sys,json,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import check_terminal_rebuild_certificates as c
from check_whir_handoff import add,sub,mul
from verify_whir_toy import ZERO,ONE
from native_folded_v2 import compile_weighted
from table_constraint_whir import selectors
from pq384_shift import eq_point
import pq384_global_bus as bus
for k,v in dict(OPS={'add':add,'sub':sub,'mul':mul},ZERO=ZERO,ONE=ONE,mul=mul,compile_weighted=compile_weighted,selectors=selectors,eq_point=eq_point,bus=bus).items():setattr(c,k,v)
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--capture',type=Path,required=True);ap.add_argument('--input-log',type=int,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--bundle',type=Path,required=True);cli=ap.parse_args()
circuit,profile,args=c.capture(cli.capture,input_log=cli.input_log)
c.require(json.loads(json.dumps(circuit))==json.loads(cli.bundle.read_text())['circuit'],'retained circuit mismatch')
cert=c.produce(circuit,args);counts=c.validate(circuit,args,cert);print(counts)
cli.output.write_text(json.dumps(cert,separators=(',',':'))+'\n')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
expected_batch=dict(rho=list(args[-1]),weights=[list(eq_point(t['tau'],t['point'])) for t in args[-2]],claims=[t['claim'] for t in args[-2]])
# Bind AST routes and residual order to independently replayed AIR data.
import check_air_program_certificates as air
import check_bus_program_formulas as auxiliary
from verify_whir_toy import P,base
for k,v in dict(P=P,ZERO=ZERO,ONE=ONE,base=base,mul=mul).items():setattr(air,k,v)
for k,v in dict(ZERO=ZERO,ONE=ONE,base=base,mul=mul,BASIS=bus.BASIS).items():setattr(auxiliary,k,v)
spec,alpha,gamma,finals,terminals,rho=args
c.require(len(spec['air']['tables'])==len(cert['programs'])==len(terminals),'AIR table coverage')
air_tables=[]
for ti,(table,program,terminal) in enumerate(zip(spec['air']['tables'],cert['programs'],terminals)):
    ins=program['instructions'];air.valid_program(ins);lookup={}
    fresh=compile_weighted(table,spec['public'],alpha,gamma,[tuple(x) for x in finals[ti]],terminal['mixing'],bus)
    c.require(ins==[list(fresh[i:i+7]) for i in range(0,len(fresh),7)],'fresh AIR program mismatch')
    for j,row in enumerate(ins):lookup.setdefault(tuple(row),j)
    constraints=bus.constraints(table);expressions=list(constraints)
    for interaction in table['interactions']:
        expressions.extend(interaction['msg']);expressions.extend(interaction['mult'])
    routes=[]
    for expr in expressions:
        register=air.locate_expr(expr,lookup,spec['public'])
        air.check_expr(expr,register,ins,spec['public'],table['width'])
        routes.append(dict(expr=expr,register=register))
    accumulation=air.accumulation(ins);air.check_accumulation(ins,accumulation,terminal['mixing'])
    c.require([r['register'] for r in routes[:len(constraints)]]==[s['residual'] for s in accumulation['steps'][:len(constraints)]],'source residual prefix')
    formulas,aux_columns=auxiliary.expected(table,spec['public'],alpha,gamma,finals[ti])
    c.require(aux_columns==bus.aux.layout(table)['aux_columns'],'auxiliary layout mismatch')
    roots=[step['residual'] for step in accumulation['steps'][len(constraints):]]
    c.require(len(roots)==len(formulas),'auxiliary coverage')
    for formula,register in zip(formulas,roots):
        auxiliary.validate_formula(formula['formula'],register,ins,table['width']+4*aux_columns,{})
        formula['register']=register
    air_tables.append(dict(bus_formulas=formulas,full_width=table['width']+4*aux_columns,width=table['width'],mixing=terminal['mixing'],expression_routes=routes,
        source_constraints=len(constraints),accumulation=accumulation,
        auxiliary_residual_count=len(accumulation['steps'])-len(constraints)))
air_output=cli.output.with_suffix('.air.json')
air_output.write_text(json.dumps(dict(public=[list(base(v)) for v in spec['public']],tables=air_tables,
    program_sha256=sha(cli.output)),separators=(',',':'))+'\n')
expected_tables=[dict(row_log=spec['log_rows'][i] if isinstance(spec['log_rows'],list) else spec['log_rows'],
    point=[list(x) for x in terminal['point']],tau=[list(x) for x in terminal['tau']],
    mixing=list(terminal['mixing']),claim=list(terminal['claim'])) for i,terminal in enumerate(terminals)]
for table in expected_tables:c.require(len(table['point'])==table['row_log'],'terminal point dimension')
report=dict(expected_tables=expected_tables,air_sha256=sha(air_output),expected_batch=expected_batch,status='PASS',capture=str(cli.capture),input_log=cli.input_log,profile=profile,counts=counts,
    statement_sha256=sha(cli.capture/'statement.json'),proof_sha256=sha(cli.capture/'proof.json'),
    bundle_sha256=sha(cli.bundle),rebuild_sha256=sha(cli.output),
    scope='Full fixed-profile proof verified before replay; reconstructed circuit equals retained bundle. Structural certificate validation, not security certification.')
cli.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
