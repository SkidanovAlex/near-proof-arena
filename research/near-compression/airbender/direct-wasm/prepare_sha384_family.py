"""Project canonical checked SHA384 chain witnesses for one captured family."""
import argparse,hashlib,json
from pathlib import Path
from prepare_sha384_committed import capture_input
from prepare_sha384_batched import metadata,public_tape

def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--chain-directory');a=p.parse_args();out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);capture=json.loads(Path(a.capture).read_text());message,fixed=capture_input(capture);assert 1<=len(message)<=1024
    (out/'message.bin').write_bytes(message);(out/'fixed-framing.json').write_text(json.dumps(fixed,separators=(',',':')))
    if not a.chain_directory:return
    chain=Path(a.chain_directory);report=json.loads((chain/'chain.json').read_text());count=(len(message)+16)//128+1;padded=message+b'\x80'+bytes((111-len(message))%128)+(8*len(message)).to_bytes(16,'big')
    assert report['message_bytes']==list(message) and report['padded_bytes']==list(padded) and report['digest_bytes']==list(hashlib.sha384(message).digest()) and report['block_count']==count and report['chain_boundary_check']
    spec=json.loads((out/'spec.json').read_text());full=public_tape(message);assert spec['public']==list(hashlib.sha384(message).digest())+[1,0,0,0]+full[-36:]
    core=[];endpoint=[];hashes=[]
    for b in range(count):
        raw=(chain/f'block-{b}'/'source-00-rows.json').read_bytes();hashes.append(hashlib.sha256(raw).hexdigest());rows=json.loads(raw)['rows'];assert len(rows)==128 and all(len(r)==6944 for r in rows)
        for phase,row in enumerate(rows[:80]):
            assert row[5152:5280]==[int(i==phase) for i in range(128)];core.append(row[:5232]+[1,b])
        endpoint.append(rows[79][5280:]+metadata(b,1,count))
    while len(core)<1<<spec['log_rows'][0]:core.append([0]*5234)
    while len(endpoint)<1<<spec['log_rows'][1]:endpoint.append([0]*1664+metadata(0,0,count))
    inputs=[[(b>>i)&1 for b in message for i in range(8)],[0]*(8*len(message))]
    for ti,rows in enumerate([core,endpoint,inputs]):
        assert len(rows)==1<<spec['log_rows'][ti] and all(len(r)==spec['air']['tables'][ti]['width'] for r in rows)
        (out/f'source-{ti:02d}-rows.json').write_text(json.dumps({'rows':rows},separators=(',',':')))
    record=dict(status='PASS',message_bytes=len(message),blocks=count,fixed_framing_bytes=len(fixed),witness_part_bytes=len(message)-len(fixed),public_fields=88,source_cells=sum(len(r)*len(r[0]) for r in [core,endpoint,inputs]),source_block_sha256=hashes,message_sha256=hashlib.sha256(message).hexdigest(),captured_source_proof_sha256=capture['source_proof_sha256'],canonical_chain_checked=True,scope='Actual captured framed input and canonical Lean-generated compression witnesses. No zero-knowledge or security certification; producer-to-input-root routing remains external.')
    (out/'preparation-report.json').write_text(json.dumps(record,indent=2));print(json.dumps(record,indent=2))
if __name__=='__main__':main()
