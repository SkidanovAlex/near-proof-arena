"""Materialize input and padding witnesses from an actual captured framed call.

Framing constants are fixed; part bodies remain committed input. The caller's
expected input commitment is mandatory and external to the proof verifier.
"""
import argparse,hashlib,json,struct
from pathlib import Path

def capture_input(capture):
    prefix=b'NEAR-PQ384-PRIMITIVES-V1';tag=bytes.fromhex(capture['tag_hex']);parts=[bytes.fromhex(x) for x in capture['parts_hex']]
    message=bytearray();fixed=[]
    def constant(data):
        start=len(message);message.extend(data);fixed.extend((start+i,b) for i,b in enumerate(data))
    constant(prefix);constant(struct.pack('<I',len(tag)));constant(tag);constant(struct.pack('<I',len(parts)))
    for part in parts:constant(struct.pack('<Q',len(part)));message.extend(part)
    assert bytes(message)==bytes.fromhex(capture['message_hex']);assert hashlib.sha384(message).hexdigest()==capture['expected_digest_hex']
    return bytes(message),fixed

def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--batched-directory');a=p.parse_args();out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);capture=json.loads(Path(a.capture).read_text());message,fixed=capture_input(capture)
    (out/'message.bin').write_bytes(message);(out/'fixed-framing.json').write_text(json.dumps(fixed,separators=(',',':')))
    if not a.batched_directory:return
    src=Path(a.batched_directory);spec=json.loads((out/'spec.json').read_text());old=json.loads((src/'spec.json').read_text());count=(len(message)+16)//128+1
    assert spec['public']==list(hashlib.sha384(message).digest())+[1,0,0,0]+old['public'][-36:];assert len(spec['public'])==88
    for i in (0,1):(out/f'source-{i:02d}-rows.json').write_bytes((src/f'source-{i:02d}-rows.json').read_bytes())
    bits=lambda data:[(b>>i)&1 for b in data for i in range(8)]
    inputrows=[bits(message),[0]*(8*len(message))]
    padded=message+b'\x80'+bytes((111-len(message))%128)+(8*len(message)).to_bytes(16,'big');assert len(padded)==128*count
    padrows=[bits(padded[128*b:128*(b+1)])+[int(i==b) for i in range(count)] for b in range(count)]
    while len(padrows)<1<<spec['log_rows'][3]:padrows.append([0]*(1024+count))
    for i,rows in [(2,inputrows),(3,padrows)]:
        assert len(rows)==1<<spec['log_rows'][i] and all(len(r)==spec['air']['tables'][i]['width'] for r in rows)
        (out/f'source-{i:02d}-rows.json').write_text(json.dumps({'rows':rows},separators=(',',':')))
    report={'profile':'committed-input-framed-hash-v1','message_bytes':len(message),'blocks':count,'fixed_framing_bytes':len(fixed),'private_part_bytes':len(message)-len(fixed),'public_fields':88,'public_fixed_width_bytes':352,'input_table_index':2,'input_shape':[2,8*len(message)],'padding_shape':[len(padrows),1024+count],'old_batched_cells':sum((1<<n)*t['width'] for n,t in zip(old['log_rows'],old['air']['tables'])),'total_cells':sum((1<<n)*t['width'] for n,t in zip(spec['log_rows'],spec['air']['tables'])),'message_sha256':hashlib.sha256(message).hexdigest(),'captured_source_proof_sha256':capture['source_proof_sha256'],'spec_sha256':hashlib.sha256((out/'spec.json').read_bytes()).hexdigest(),'scope':'SHA384 of externally committed framed input; recursive producer-to-input commitment routing is not implemented; natural routing semantic refinement pending.'}
    (out/'preparation-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
