"""Check canonical multiblock boundaries, exact natural bus traffic, and one proof.
The expected AIR is an externally supplied canonical Lean export, never proof-selected.
"""
import argparse,collections,copy,hashlib,json,sys,time
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-dir',required=True);p.add_argument('--proof-dir',required=True);a=p.parse_args()
    sys.path.append(a.reference_dir);sys.path.append(str(Path(a.reference_dir).parent/'generic-air'))
    import reference as ref
    import pq384_global_bus as bus
    import pq384_global_bus_codec as codec
    fixture=Path(a.fixture_dir);out=Path(a.proof_dir);expected=json.loads((fixture/'spec.json').read_text());statement=json.loads((out/'statement.json').read_text());proof=json.loads((out/'proof.json').read_text());spec=statement['spec'];roots=[bytes.fromhex(r) for r in statement['roots']]
    for key in ('air','public','log_rows'):assert spec[key]==expected[key]
    message=bytes(spec['public'][:-48]);assert bytes(spec['public'][-48:])==hashlib.sha384(message).digest()
    tables=spec['air']['tables'];rows=[json.loads((fixture/f'source-{i:02d}-rows.json').read_text())['rows'] for i in range(len(tables))]
    # The base compression prefix is separately checked by the actual proof.
    # Independently inspect all natural bus multiplicities, without field sums.
    def counts(traces):
        result=collections.Counter()
        for table,trace in zip(tables,traces):
            for r in range(len(trace)):
                for interaction in table['interactions']:
                    bits=[ref.evaluate(e,trace,r,spec['public']) for e in interaction['mult']]
                    assert all(b in (0,1) for b in bits)
                    mult=sum((1<<k) for k,b in enumerate(bits) if b==1)
                    if mult:
                        msg=tuple(ref.evaluate(e,trace,r,spec['public']) for e in interaction['msg'])
                        result[(interaction['bus'],msg)]+=mult*(1 if interaction['send'] else -1)
        return {k:v for k,v in result.items() if v}
    assert not counts(rows)
    boundary_checks=0
    for ti,(table,trace) in enumerate(zip(tables,rows)):
        boundary_count=128+(32 if ti==0 else 0)+(48 if ti==len(tables)-1 else 0)
        bit_count=sum(len(x['mult']) for x in table['interactions'])
        end=len(table['constraints'])-bit_count
        boundaries=table['constraints'][end-boundary_count:end]
        for r in range(128):
            for e in boundaries:
                assert ref.evaluate(e,trace,r,spec['public'])==0
                boundary_checks+=1
    # Mutate actual padded-byte bits at row zero, independently of transcript binding.
    window=[1440,576,1776,1840,1904,1968,2032,2096,2160,1232,2224,2288,2352,2416,0,2480]
    padding_negatives=0
    for gi in (len(message),len(message)+1,len(tables)*128-1):
        ti,j=divmod(gi,128);trace=copy.deepcopy(rows[ti]);col=window[j//8]+8*(7-j%8)
        trace[0][col]^=1
        count=128+(32 if ti==0 else 0)+(48 if ti==len(tables)-1 else 0)
        bit_count=sum(len(x['mult']) for x in tables[ti]['interactions'])
        e=tables[ti]['constraints'][len(tables[ti]['constraints'])-bit_count-count+j]
        assert ref.evaluate(e,trace,0,spec['public'])!=0
        padding_negatives+=1
    bad=copy.deepcopy(rows);bad[1][0][5280]=(bad[1][0][5280]+1)%ref.P;assert counts(bad)
    assert bus.verify(proof,spec,roots)
    wire=codec.encode(proof,spec,roots);assert codec.decode(wire,spec,roots)==proof;(out/'proof.bin').write_bytes(wire)
    negatives=1+padding_negatives
    for index in (0,len(message)-1,len(message),len(spec['public'])-1):
        altered=copy.deepcopy(spec);altered['public'][index]^=1
        try:bus.verify(proof,altered,roots)
        except (ValueError,AssertionError,IndexError,KeyError):negatives+=1
        else:raise AssertionError('changed message/digest accepted')
    for ti in range(len(tables)):
        altered=copy.deepcopy(spec);altered['air']['tables'][ti]['interactions']=[]
        try:bus.verify(proof,altered,roots)
        except (ValueError,AssertionError,IndexError,KeyError):negatives+=1
        else:raise AssertionError('removed state routing accepted')
    report=dict(status='PASS',compression_blocks=len(tables),message_bytes=len(message),public_bytes=len(spec['public']),single_multitable_proof=True,
        proof_bytes_including_source_roots=len(wire),proof_sha256=hashlib.sha256(wire).hexdigest(),negative_checks=negatives,
        natural_bus_balance_checked_on_actual_witness=True,hashlib_digest_match=True,boundary_residual_checks=boundary_checks,padding_bit_mutations_rejected=padding_negatives,
        scope='All compression, padding, IV, digest and state-link constraints under one diagnostic AIR proof. Randomized bus fingerprint soundness and PCS soundness remain conditional; not a recursive verifier or 128-bit security claim.')
    (out/'multiblock-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
