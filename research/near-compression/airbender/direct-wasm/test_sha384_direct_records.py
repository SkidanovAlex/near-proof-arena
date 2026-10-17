"""Independent exact padded-block records and natural bus balance checks."""
import argparse,collections,json,sys
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);a=p.parse_args();sys.path.append(str(Path(a.reference_dir).parent/'generic-air'));import reference as ref
    src=Path(a.fixture_directory);spec=json.loads((src/'spec.json').read_text());rows=[json.loads((src/f'source-{i:02d}-rows.json').read_text())['rows'] for i in range(3)];msg=(src/'message.bin').read_bytes();pad=msg+b'\x80'+bytes((111-len(msg))%128)+(8*len(msg)).to_bytes(16,'big')
    table=spec['air']['tables'][2];checks=0
    for r in range(2):
        for e in table['constraints']:assert ref.evaluate(e,rows[2],r,spec['public'])==0;checks+=1
    for b,it in enumerate(table['interactions']):
        expected=[b]+[int.from_bytes(pad[128*b+8*w+6-2*l:128*b+8*w+8-2*l],'big') for w in range(16) for l in range(4)]
        actual=[ref.evaluate(e,rows[2],0,spec['public']) for e in it['msg']];assert actual==expected
        assert [ref.evaluate(e,rows[2],0,spec['public']) for e in it['mult']]==[1]
        assert [ref.evaluate(e,rows[2],1,spec['public']) for e in it['mult']]==[0]
    tally=collections.Counter();sent=collections.Counter();recv=collections.Counter()
    for table,trace in zip(spec['air']['tables'],rows):
        for r in range(len(trace)):
            for it in table['interactions']:
                bits=[ref.evaluate(e,trace,r,spec['public']) for e in it['mult']];assert all(v in(0,1) for v in bits);mult=sum((1<<j)*v for j,v in enumerate(bits))
                if mult:
                    message=tuple(ref.evaluate(e,trace,r,spec['public']) for e in it['msg']);tally[(it['bus'],message)]+=mult*(1 if it['send'] else -1);(sent if it['send'] else recv)[it['bus']]+=mult
    for b,send,message in ref.public_messages(spec['air'],spec['public']):tally[(b,tuple(message))]+=1 if send else -1;(sent if send else recv)[b]+=1
    assert not any(tally.values());assert sent==recv=={0:4,1:4,2:3,3:1,4:4,5:1}
    report=dict(status='PASS',input_constraint_residuals=checks,exact_padded_block_records=4,natural_bus_sent=dict(sent),natural_bus_received=dict(recv),scope='Canonical exported Expr differential, actual witness natural balance; no cryptographic claim.')
    (src/'record-checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
