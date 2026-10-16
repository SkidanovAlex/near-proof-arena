"""Endpoint-split exact natural routing, independent proof, and adversarial checks."""
import argparse,collections,copy,hashlib,json,os,subprocess,sys
from pathlib import Path
from prepare_sha384_endpoint import metadata

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--proof-directory',required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--folded-library',required=True);p.add_argument('--fft-library',required=True);a=p.parse_args();sys.path.append(a.reference_dir);sys.path.append(str(Path(a.reference_dir).parent/'generic-air'))
    import reference as ref
    import pq384_global_bus as bus
    import pq384_global_bus_codec as codec
    inp=Path(a.fixture_directory);out=Path(a.proof_directory);canonical=json.loads((inp/'spec.json').read_text());statement=json.loads((out/'statement.json').read_text());spec=statement['spec'];proof=json.loads((out/'proof.json').read_text());roots=[bytes.fromhex(r) for r in statement['roots']]
    for key in ('air','public','log_rows'):assert canonical[key]==spec[key]
    tables=spec['air']['tables'];count=len(tables)-1;traces=[json.loads((inp/f'source-{ti:02d}-rows.json').read_text())['rows'] for ti in range(len(tables))]
    def counts(rows):
        values=collections.Counter();sent=collections.Counter();recv=collections.Counter()
        for table,trace in zip(tables,rows):
            for ri in range(len(trace)):
                for interaction in table['interactions']:
                    bits=[ref.evaluate(e,trace,ri,spec['public']) for e in interaction['mult']];assert all(b in (0,1) for b in bits)
                    mult=sum(1<<i for i,b in enumerate(bits) if b==1)
                    if mult:
                        msg=tuple(ref.evaluate(e,trace,ri,spec['public']) for e in interaction['msg']);key=(interaction['bus'],msg)
                        values[key]+=mult*(1 if interaction['send'] else -1)
                        (sent if interaction['send'] else recv)[interaction['bus']]+=mult
        for busid,send,msg in ref.public_messages(spec['air'],spec['public']):
            values[(busid,tuple(msg))]+=1 if send else -1;(sent if send else recv)[busid]+=1
        return {k:v for k,v in values.items() if v},dict(sent),dict(recv)
    balance,sent,recv=counts(traces);assert not balance;assert sent==recv=={0:count,1:count,2:count-1,3:1}
    endpoint_checks=0
    for r in range(len(traces[-1])):
        for e in tables[-1]['constraints']:
            assert ref.evaluate(e,traces[-1],r,spec['public'])==0;endpoint_checks+=1
    assert bytes(spec['public'][-52:-4])==hashlib.sha384(bytes(spec['public'][:-52])).digest();assert spec['public'][-4:]==[1,0,0,0]
    assert bus.verify(proof,spec,roots);wire=codec.encode(proof,spec,roots);assert codec.decode(wire,spec,roots)==proof;(out/'proof.bin').write_bytes(wire)
    negatives=0
    for index in (1665,1666,1667):
        bad=copy.deepcopy(traces[-1]);bad[0][index]=(bad[0][index]+1)%ref.P
        assert any(ref.evaluate(e,bad,0,spec['public']) for e in tables[-1]['constraints']);negatives+=1
    for index in (0,len(spec['public'])-52,len(spec['public'])-4):
        bad=copy.deepcopy(spec);bad['public'][index]^=1
        try:bus.verify(proof,bad,roots)
        except (AssertionError,ValueError,IndexError,KeyError):negatives+=1
        else:raise AssertionError('changed statement accepted')
    # Fresh malformed routing preserves all endpoint arithmetic/local constraints.
    bad=copy.deepcopy(traces[-1]);bad[0][-4:]=metadata(1,1,count)
    assert all(ref.evaluate(e,bad,r,spec['public'])==0 for r in range(len(bad)) for e in tables[-1]['constraints'])
    malformed=traces[:-1]+[bad];assert counts(malformed)[0];negatives+=1
    invalid=out/'duplicate-tag-fixture';invalid.mkdir(exist_ok=True);(invalid/'spec.json').write_text(json.dumps(canonical,separators=(',',':')))
    for ti,trace in enumerate(malformed):(invalid/f'source-{ti:02d}-rows.json').write_text(json.dumps({'rows':trace},separators=(',',':')))
    invalidproof=out/'duplicate-tag-proof';env=os.environ.copy();env['PYTHONPATH']=a.reference_dir
    command=[sys.executable,str(Path(a.reference_dir)/'run_pq384_global_bus.py'),'--reference-dir',a.reference_dir,'--spec',str(invalid/'spec.json'),'--source-directory',str(invalid),
        '--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(invalidproof)]
    run=subprocess.run(command,env=env,capture_output=True,text=True);(out/'duplicate-tag-run.log').write_text(run.stdout+run.stderr)
    assert run.returncode!=0 and (invalidproof/'proof.json').exists()
    badproof=json.loads((invalidproof/'proof.json').read_text());badstatement=json.loads((invalidproof/'statement.json').read_text());badroots=[bytes.fromhex(r) for r in badstatement['roots']]
    assert bus.verify_local(badproof,badstatement['spec'],badroots)
    try:bus.verify(badproof,badstatement['spec'],badroots)
    except (AssertionError,ValueError):negatives+=1
    else:raise AssertionError('fresh duplicate-tag full proof accepted')
    report=dict(status='PASS',tables=len(tables),core_width=5280,core_rows=128,endpoint_width=1668,endpoint_rows=len(traces[-1]),
        exact_natural_bus_sent=sent,exact_natural_bus_received=recv,endpoint_residual_checks=endpoint_checks,negative_checks=negatives,
        fresh_duplicate_tag_local_and_PCS_accept=True,fresh_duplicate_tag_global_reject=True,hashlib_digest_match=True,
        proof_bytes_including_source_roots=len(wire),baseline_multiblock_bytes=1508054,proof_bytes_saved=1508054-len(wire),proof_sha256=hashlib.sha256(wire).hexdigest(),
        scope='Canonical split AIR diagnostic; exact witness routing checked. Full Lean routing-to-hash composition and cryptographic soundness remain separate obligations.')
    (out/'endpoint-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
