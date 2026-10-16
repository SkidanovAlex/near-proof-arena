"""Differential compiler checks and candidate Ext8 terminal geometry.
No GKR proof, native round kernel, PCS proof, or security certification.
"""
import argparse, hashlib, json, random, subprocess, sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'generic-air'))
import pq384_ext8_reference as f
import pq384_global_bus as bus
from pq384_ext8_terminal_compile import compile_ext8_terminal,compile_weighted
from pq384_terminal_compile import compile_terminal
from pq384_terminal_gkr import layer_circuit


def environment(point,tau):
    first=last=eq=f.ONE
    for x,y in zip(point,tau):
        first=f.mul(first,f.sub(f.ONE,x));last=f.mul(last,x)
        eq=f.mul(eq,f.add(f.mul(x,y),f.mul(f.sub(f.ONE,x),f.sub(f.ONE,y))))
    return [first,last,f.sub(f.ONE,last)],eq


def raw_program(program,current,nxt,sels):
    values=[]
    assert len(program)%11==0
    for i in range(0,len(program),11):
        op,x,y,*constant=program[i:i+11]
        if op==0:value=tuple(constant)
        elif op==1:value=current[x]
        elif op==2:value=nxt[x]
        elif op in (3,4,5):value=sels[op-3]
        else:
            assert x<len(values) and y<len(values)
            value={6:f.add,7:f.sub,8:f.mul}[op](values[x],values[y])
        values.append(value)
    return values[-1]


def dag_value(circuit,private):
    values=[]
    for node in circuit['nodes']:
        if node[0]=='const':v=tuple(node[1:])
        elif node[0]=='input':v=private[node[1]]
        else:v={'add':f.add,'sub':f.sub,'mul':f.mul}[node[0]](values[node[1]],values[node[2]])
        values.append(v)
    return values[circuit['root']]


def layer_value(layout,private):
    values=private+[f.ZERO]*(layout['input_size']-len(private))
    for i,v in layout['constants'].items():values[i]=v
    for layer in layout['layers']:
        values=[{'add':f.add,'sub':f.sub,'mul':f.mul}[op](values[x],values[y]) for op,x,y in layer]
    return values[layout['root']]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    source=Path('results/pq384-literal193-gkr-fixed13/statement.json');spec=json.loads(source.read_text())['spec']
    rng=random.Random(903108)
    def scalar(degree):return tuple(rng.randrange(f.P) for _ in range(degree))
    def inputs(degree):
        alpha,gamma,rho=(scalar(degree) for _ in range(3))
        finals=[[scalar(degree) for _ in t['interactions']] for t in spec['air']['tables']]
        terminals=[dict(point=[scalar(degree) for _ in range(n)],tau=[scalar(degree) for _ in range(n)],mixing=scalar(degree),claim=scalar(degree)) for n in spec['log_rows']]
        return alpha,gamma,finals,terminals,rho
    # Exact legacy output regression, independently load the pre-edit compiler.
    old=subprocess.run(['git','show','04eaa8e31:research/near-compression/airbender/direct-wasm/pq384_terminal_compile.py'],check=True,capture_output=True,text=True).stdout
    legacy={};exec(compile(old,'legacy_terminal_compile','exec'),legacy)
    legacy_cases=0;legacy_geometry=None
    for _ in range(3):
        args=inputs(4)
        legacy_circuit=legacy['compile_terminal'](spec,*args)
        assert compile_terminal(spec,*args)==legacy_circuit
        legacy_layout=layer_circuit(legacy_circuit)
        legacy_geometry=dict(private_capacity=legacy_circuit['private_input_capacity'],input_size=legacy_layout['input_size'],layers=len(legacy_layout['layers']))
        legacy_cases+=1
    alpha,gamma,finals,terminals,rho=inputs(8)
    rejected=0
    for operation in (
        lambda: compile_ext8_terminal(spec,alpha,gamma,finals,terminals[:-1],rho),
        lambda: compile_terminal(spec,alpha,gamma,finals,terminals,rho,field=f),
        lambda: compile_terminal(spec,alpha,gamma,finals,terminals,rho,field=f,program_compiler=lambda *args:[0]),
    ):
        try:operation()
        except ValueError:rejected+=1
        else:raise AssertionError('malformed compiler input accepted')
    checks=0;geometries=[]
    for batch in (f.ZERO,f.ONE,rho):
        circuit=compile_ext8_terminal(spec,alpha,gamma,finals,terminals,batch)
        layout=layer_circuit(circuit,field=f)
        blocks={b['table']:b for b in circuit['input_blocks']}
        programs=[compile_weighted(t,spec['public'],alpha,gamma,finals[i],terminals[i]['mixing'],bus) for i,t in enumerate(spec['air']['tables'])]
        for private in ([f.ZERO]*circuit['private_input_capacity'],[scalar(8) for _ in range(circuit['private_input_capacity'])]):
            expected=f.ZERO;weight=f.ONE
            for i,t in enumerate(spec['air']['tables']):
                b=blocks[i];offset=b['offset'];width=b['column_capacity'];sels,eq=environment(terminals[i]['point'],terminals[i]['tau'])
                raw=raw_program(programs[i],private[offset:offset+width],private[offset+width:offset+2*width],sels)
                expected=f.add(expected,f.mul(weight,f.sub(f.mul(eq,raw),terminals[i]['claim'])))
                weight=f.mul(weight,batch)
            assert dag_value(circuit,private)==expected
            assert layer_value(layout,private)==expected
            checks+=1
        layer_input_sizes=[layout['input_size']]+[len(layer) for layer in layout['layers'][:-1]]
        gkr_logs=[size.bit_length()-1 for size in reversed(layer_input_sizes)]
        geometries.append(dict(gkr_layer_logs=gkr_logs,gkr_error_numerator=sum(4*m+1 for m in gkr_logs),
            raw_gkr_field_elements=sum(6*m+2 for m in gkr_logs),raw_gkr_scalar_bytes=32*sum(6*m+2 for m in gkr_logs),batch='zero' if batch==f.ZERO else 'one' if batch==f.ONE else 'random',
            registers=[len(p)//11 for p in programs],nodes=len(circuit['nodes']),live_nodes=len(circuit['live_nodes']),
            input_blocks=circuit['input_blocks'],private_capacity=circuit['private_input_capacity'],input_size=layout['input_size'],
            minimum_input_log=layout['input_size'].bit_length()-1,layer_sizes=[len(layer) for layer in layout['layers']]))
    report=dict(status='EXT8_TERMINAL_COMPILER_CANDIDATE_DIFFERENTIAL_PASS',statement=str(source),statement_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        legacy_reference='04eaa8e31',legacy_geometry=legacy_geometry,legacy_compiler_sha256=hashlib.sha256(old.encode()).hexdigest(),exact_ext4_compiler_comparisons=legacy_cases,
        ext8_raw_program_dag_layer_comparisons=checks,malformed_inputs_rejected=rejected,geometries=geometries,
        limitations=['No Ext8 native round kernel, GKR prover/transcript, PCS integration or full slice proof.',
            'Independent unoptimized instruction evaluation checks DAG/layer transforms; it is not independent universal formula-generator semantics.',
            'Synthetic terminal challenges/finals on the actual 193-instruction AIR; no authenticated Ext8 transcript.',
            'No universal Lean compiler refinement or secure size/security claim.'])
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='geometries'},indent=2))
    print(json.dumps([dict(batch=g['batch'],private_capacity=g['private_capacity'],minimum_input_log=g['minimum_input_log'],layers=len(g['layer_sizes'])) for g in geometries]))

if __name__=='__main__':main()
