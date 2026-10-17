"""Mandatory input bindings, wire corruption, and fresh full-proof negative cases."""
import argparse,copy,json,subprocess,sys
from pathlib import Path
from verify_sha384_shared import verify

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--proof-directory',required=True);p.add_argument('--rs-binary');p.add_argument('--folded-library');p.add_argument('--fft-library');p.add_argument('--fresh-proofs',action='store_true');a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_gkr_bus as bus
    import pq384_compact_gkr_bus_codec as codec
    out=Path(a.proof_directory);src=Path(a.fixture_directory);st=json.loads((out/'statement.json').read_text());expected=json.loads((out/'expected-inputs.json').read_text());wire=(out/'proof.bin').read_bytes();assert verify(wire,st,expected);negative=[]
    def reject(name,w,s,e):
        try:verify(w,s,e)
        except (AssertionError,ValueError,IndexError,KeyError):negative.append(name)
        else:raise AssertionError(name)
    for c in range(2):
        for name,alter in [('missing-root',lambda x:x.pop('input_root')),('wrong-root',lambda x:x.update(input_root='00'*48)),('wrong-context',lambda x:x.update(input_context_hex='00')),('wrong-length',lambda x:x.update(declared_length=266)),('missing-framing',lambda x:x.update(fixed_framing=[])),('bool-framing',lambda x:x['fixed_framing'][0].__setitem__(1,True))]:
            bad=copy.deepcopy(expected);alter(bad['inputs'][c]);reject(f'call{c}-{name}',wire,st,bad)
    bad=copy.deepcopy(expected);bad['inputs'].reverse();reject('swapped-call-roots',wire,st,bad)
    bad=copy.deepcopy(expected);bad['inputs'].pop();reject('missing-second-caller',wire,st,bad)
    bad=copy.deepcopy(expected);bad['air_sha384']='00'*48;reject('wrong-AIR-config',wire,st,bad)
    for name,w in [('truncated-wire',wire[:-1]),('trailing-wire',wire+b'\0'),('root-wire',wire[:6]+bytes([wire[6]^1])+wire[7:]),('opening-wire',wire[:-1]+bytes([wire[-1]^1]))]:reject(name,w,st,expected)
    for name,index,value in [('digest-bool',0,True),('digest-range',0,256),('second-digest-negative',48,-1),('second-digest-alias',48,2013265921+st['spec']['public'][48]),('changed-digest',0,st['spec']['public'][0]^1)]:
        bad=copy.deepcopy(st);bad['spec']['public'][index]=value;reject(name,wire,bad,expected)
    fresh=[]
    if a.fresh_proofs:
        assert a.rs_binary and a.folded_library and a.fft_library
        original=json.loads((src/'spec.json').read_text());rows=[json.loads((src/f'source-{i:02d}-rows.json').read_text())['rows'] for i in range(6)]
        def prove(name,changed):
            fixture=out/(name+'-fixture');fixture.mkdir(exist_ok=True);(fixture/'spec.json').write_text(json.dumps(original,separators=(',',':')))
            for ti,tr in enumerate(changed):(fixture/f'source-{ti:02d}-rows.json').write_text(json.dumps({'rows':tr},separators=(',',':')))
            dest=out/(name+'-proof');cmd=[sys.executable,str(Path(a.reference_dir)/'run_pq384_gkr_bus.py'),'--reference-dir',a.reference_dir,'--spec',str(fixture/'spec.json'),'--source-directory',str(fixture),'--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--source-zero-cache',str(out/'source-00-cache'),'--output-dir',str(dest)]
            with (out/(name+'.log')).open('w') as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
            assert (dest/'proof.json').exists(),name
            statement=json.loads((dest/'statement.json').read_text());proof=json.loads((dest/'proof.json').read_text());roots=[bytes.fromhex(v) for v in statement['roots']]
            return r,statement,proof,roots,dest
        # A fresh, genuinely valid component under a different source commitment:
        # unused second input row remains Boolean, sends no records.
        changed=copy.deepcopy(rows);changed[5][1][0]=1
        result,s,pr,rt,dest=prove('fresh-different-call1-root',changed);assert result.returncode==0 and bus.verify(pr,s['spec'],rt)
        w=codec.encode(pr,s['spec'],rt);(dest/'proof.bin').write_bytes(w);reject('fresh-valid-wrong-expected-call1-root',w,s,expected)
        fresh.append(dict(name='fresh-different-call1-root',full_underlying_proof_accepts=True,component_rejects=True))
        # Bit-valid exact2 -> exact1 fanout. All local constraints remain valid;
        # fresh auxiliaries/PCS must not replace the global fingerprint check.
        changed=copy.deepcopy(rows);changed[2][0][2:4]=[1,0]
        result,s,pr,rt,dest=prove('fresh-fanout-two-to-one',changed);assert result.returncode!=0 and bus.verify_local(pr,s['spec'],rt)
        try:bus.verify(pr,s['spec'],rt)
        except (AssertionError,ValueError):negative.append('fresh-local-and-PCS-valid-fanout-global-reject')
        else:raise AssertionError('missing shared-node use accepted')
        fresh.append(dict(name='fresh-fanout-two-to-one',local_and_PCS_accepts=True,global_fingerprint_rejects=True))
    report=dict(status='PASS',negative_tests=negative,fresh_proofs=fresh,scope='Mandatory caller bindings and complete diagnostic verification; exact natural balance and formal semantic refinement remain separately scoped.')
    (out/('shared-fresh-negatives.json' if a.fresh_proofs else 'shared-negatives.json')).write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
