"""Capture one real source Merkle-node hash from an accepted full verifier run."""
import argparse,hashlib,json,struct,sys
from pathlib import Path


def frame(tag,parts,prefix):
    return prefix+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(struct.pack('<Q',len(x))+x for x in parts)


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--input-directory',required=True);p.add_argument('--output-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_primitives as primitive
    import pq384_seed_gkr_bus as bus
    inp=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    proof=json.loads((inp/'proof.json').read_text());s=json.loads((inp/'statement.json').read_text());config=bus.configure(s['spec']['air']);captured=[];original=primitive.hash_parts
    def observe(tag,*parts):
        digest=original(tag,*parts)
        if not captured and tag==b'merkle/node' and parts[0].startswith(b'NEAR-PQ384-RS-PACKED-V2/'):
            message=frame(tag,parts,primitive.PREFIX);assert hashlib.sha384(message).digest()==digest
            captured.append(dict(tag_hex=tag.hex(),parts_hex=[x.hex() for x in parts],message_hex=message.hex(),expected_digest_hex=digest.hex(),message_bytes=len(message),sha384_compression_blocks=(len(message)+17+127)//128))
        return digest
    primitive.hash_parts=observe
    try:assert bus.verify(proof,s['spec'],[bytes.fromhex(x) for x in s['roots']],config)
    finally:primitive.hash_parts=original
    assert len(captured)==1;record=captured[0];record.update(source_proof_sha256=hashlib.sha256((inp/'proof.json').read_bytes()).hexdigest(),source_statement_sha256=hashlib.sha256((inp/'statement.json').read_bytes()).hexdigest(),source_profile=proof['profile'],source_verifier_accepts=True)
    (out/'message.bin').write_bytes(bytes.fromhex(record['message_hex']));(out/'captured-hash.json').write_text(json.dumps(record,indent=2));print(json.dumps({k:record[k] for k in ['message_bytes','sha384_compression_blocks','expected_digest_hex']}))

if __name__=='__main__':main()
