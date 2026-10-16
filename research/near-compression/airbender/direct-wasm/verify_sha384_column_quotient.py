"""Mandatory original-AIR-derived quotient verification, never proof-selected mapping."""
import copy
import pq384_column_quotient as quotient

def derived_spec(original_spec):
    from run_pq384_global_bus import choose_packing
    import pq384_global_bus as bus
    air,plans=quotient.quotient(original_spec['air'])
    spec={k:copy.deepcopy(original_spec[k]) for k in ('public','log_rows')};spec['air']=air;spec['terminal_degree']=1
    spec['source_packings']=[choose_packing(n,t['width']) for n,t in zip(spec['log_rows'],air['tables'])]
    spec['aux_packings']=[choose_packing(n,4*bus.aux.layout(t)['aux_columns']) if bus.aux.layout(t)['aux_columns'] else 0 for n,t in zip(spec['log_rows'],air['tables'])]
    return spec

def verify(proof,original_spec,roots):
    import pq384_global_bus as bus
    return bus.verify(proof,derived_spec(original_spec),roots)

if __name__=='__main__':
    import argparse,json,sys
    from pathlib import Path
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--original-spec',required=True);p.add_argument('--proof-dir',required=True);p.add_argument('--binary',action='store_true');a=p.parse_args();sys.path.append(a.reference_dir)
    out=Path(a.proof_dir);statement=json.loads((out/'statement.json').read_text());original=json.loads(Path(a.original_spec).read_text());assert derived_spec(original)==statement['spec']
    roots=[bytes.fromhex(r) for r in statement['roots']]
    if a.binary:
        import pq384_global_bus_codec as codec
        proof=codec.decode((out/'proof.bin').read_bytes(),derived_spec(original),roots)
    else:proof=json.loads((out/'proof.json').read_text())
    assert verify(proof,original,roots)
    print('PASS: proof verified against deterministic quotient of externally supplied original AIR')
