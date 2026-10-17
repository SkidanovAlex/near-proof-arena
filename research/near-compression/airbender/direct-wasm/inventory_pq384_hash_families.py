"""Actual accepted verifier framing families, full-input equality deduplication."""
import argparse,collections,hashlib,json,struct,sys
from pathlib import Path

def framed(prefix,tag,parts):
    return prefix+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(struct.pack('<Q',len(p))+p for p in parts)

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--input-directory',required=True);p.add_argument('--output-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_primitives as primitive
    import pq384_seed_gkr_bus as bus
    src=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    statement=json.loads((src/'statement.json').read_text());proof=json.loads((src/'proof.json').read_text());config=bus.configure(statement['spec']['air']);code=primitive.hash_parts.__code__;families={};seen=set();pending={}
    def observe(f,event,arg):
        if f.f_code is not code:return
        if event=='call':
            tag=f.f_locals['tag'];parts=f.f_locals['parts'];key=(tag,tuple(map(len,parts)));message=framed(primitive.PREFIX,tag,parts);blocks=(len(message)+144)//128
            if key not in families:
                families[key]=dict(tag=tag.decode('ascii'),part_lengths=list(map(len,parts)),message_bytes=len(message),compression_blocks=blocks,calls=0,unique_calls=0,representative=dict(tag_hex=tag.hex(),parts_hex=[v.hex() for v in parts],message_hex=message.hex(),expected_digest_hex=hashlib.sha384(message).hexdigest(),message_bytes=len(message),sha384_compression_blocks=blocks))
            row=families[key];row['calls']+=1
            exact=(tag,parts)
            if exact not in seen:seen.add(exact);row['unique_calls']+=1
            pending[id(f)]=hashlib.sha384(message).digest()
        elif event=='return':assert pending.pop(id(f))==arg
    sys.setprofile(observe)
    try:assert bus.verify(proof,statement['spec'],[bytes.fromhex(x) for x in statement['roots']],config)
    finally:sys.setprofile(None)
    assert not pending
    provenance=dict(source_proof_sha256=hashlib.sha256((src/'proof.json').read_bytes()).hexdigest(),source_statement_sha256=hashlib.sha256((src/'statement.json').read_bytes()).hexdigest(),source_profile=proof['profile'],source_verifier_accepts=True)
    rows=sorted(families.values(),key=lambda r:(-r['calls'],r['message_bytes'],r['tag'],r['part_lengths']))
    lengths={}
    for i,r in enumerate(rows):
        name=f'family-{i:03d}.json';capture=r.pop('representative');capture.update(provenance);(out/name).write_text(json.dumps(capture,indent=2));r['capture']=name
        r['total_blocks']=r['calls']*r['compression_blocks'];r['unique_blocks']=r['unique_calls']*r['compression_blocks'];v=lengths.setdefault(r['message_bytes'],dict(calls=0,unique_calls=0,total_blocks=0,unique_blocks=0))
        for k in v:v[k]+=r[k]
    totals={k:sum(r[k] for r in rows) for k in ('calls','unique_calls','total_blocks','unique_blocks')}
    nextrow=next(r for r in rows if r['message_bytes']!=376 and 1<=r['message_bytes']<=1024)
    report=dict(status='PASS',**provenance,totals=totals,families=rows,lengths={str(k):v for k,v in sorted(lengths.items())},selected_next_family=nextrow,scope='Trusted configuration setup excluded; exact actual input families, not recursive circuit coverage or security certification. Fixed-length AIR specialization must separately bind framing bytes and external root.')
    (out/'inventory.json').write_text(json.dumps(report,indent=2));print(json.dumps(dict(totals=totals,selected=nextrow,top=rows[:8]),indent=2))
if __name__=='__main__':main()
