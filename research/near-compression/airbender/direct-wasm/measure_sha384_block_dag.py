"""Exact (input chaining state, block) reuse in the actual accepted verifier.

This is measured execution, not a recursive AIR or a hash soundness theorem.
Full keys are compared; no digest collision assumption is used for deduplication.
"""
import argparse,ctypes,hashlib,json,struct,sys
from pathlib import Path
from inventory_pq384_hash_families import framed

class Probe:
    def __init__(self,path):
        self.lib=ctypes.CDLL(path);self.f=self.lib.near_sha384_states
        self.f.argtypes=[ctypes.POINTER(ctypes.c_ubyte),ctypes.c_size_t,ctypes.POINTER(ctypes.c_uint64),ctypes.c_size_t];self.f.restype=ctypes.c_int
    def run(self,message):
        padded=message+b'\x80'+bytes((111-len(message))%128)+(8*len(message)).to_bytes(16,'big');n=len(padded)//128
        src=(ctypes.c_ubyte*len(padded)).from_buffer_copy(padded);out=(ctypes.c_uint64*(8*(n+1)))();assert self.f(src,len(padded),out,len(out))==0
        states=[tuple(out[8*i:8*(i+1)]) for i in range(n+1)];assert struct.pack('>6Q',*states[-1][:6])==hashlib.sha384(message).digest()
        return padded,states

def layout(blocks):
    core=1<<max(1,(80*blocks-1).bit_length());endpoint=1<<max(1,(blocks-1).bit_length())
    return dict(core_rows=core,active_core_rows=80*blocks,padding_core_rows=core-80*blocks,endpoint_rows=endpoint,source_cells=core*5234+endpoint*1668)

def batched(blocks,chunk):
    groups=[chunk]*(blocks//chunk)+([blocks%chunk] if blocks%chunk else []);cost=[layout(n) for n in groups]
    return dict(blocks=blocks,chunk_blocks=chunk,batches=len(groups),**{k:sum(v[k] for v in cost) for k in cost[0]},peak_raw_source_bytes=4*max(v['source_cells'] for v in cost),largest_source_degree=max(v['core_rows']*128 for v in cost),profile_supported=max(v['core_rows']*128 for v in cost)<=262144)

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--input-directory',required=True);p.add_argument('--probe-library',required=True);p.add_argument('--lean-chain',action='append',default=[]);p.add_argument('--output-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_primitives as primitive
    import pq384_seed_gkr_bus as bus
    probe=Probe(a.probe_library);leanchecks=0
    for source in a.lean_chain:
        x=json.loads(Path(source).read_text());padded,states=probe.run(bytes(x['message_bytes']));assert list(padded)==x['padded_bytes']
        for i,row in enumerate(x['blocks']):assert states[i]==tuple(row['initial_words']) and states[i+1]==tuple(row['output_words']);leanchecks+=1
    src=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);statement=json.loads((src/'statement.json').read_text());proof=json.loads((src/'proof.json').read_text());config=bus.configure(statement['spec']['air'])
    exactcalls={};calls=[];exactblocks={};records=[];pending={};code=primitive.hash_parts.__code__;naive_blockbytes=set()
    def observe(f,event,arg):
        if f.f_code is not code:return
        if event=='call':
            tag=f.f_locals['tag'];parts=f.f_locals['parts'];key=(tag,parts)
            if key not in exactcalls:
                message=framed(primitive.PREFIX,tag,parts);padded,states=probe.run(message);ids=[]
                for i in range(len(states)-1):
                    block=padded[128*i:128*(i+1)];naive_blockbytes.add(block);before=struct.pack('>8Q',*states[i]);after=struct.pack('>8Q',*states[i+1]);blockkey=before+block
                    if blockkey not in exactblocks:exactblocks[blockkey]=len(records);records.append(blockkey+after)
                    node=exactblocks[blockkey];assert records[node][192:]==after;ids.append(node)
                exactcalls[key]=len(calls);calls.append(dict(tag=tag.decode('ascii'),parts_hex=[v.hex() for v in parts],message_bytes=len(message),digest_hex=hashlib.sha384(message).hexdigest(),nodes=ids,frequency=0))
            index=exactcalls[key];calls[index]['frequency']+=1;pending[id(f)]=index
        elif event=='return':assert bytes.fromhex(calls[pending.pop(id(f))]['digest_hex'])==arg
    sys.setprofile(observe)
    try:assert bus.verify(proof,statement['spec'],[bytes.fromhex(v) for v in statement['roots']],config)
    finally:sys.setprofile(None)
    assert not pending
    total=sum(len(c['nodes'])*c['frequency'] for c in calls);whole_unique=sum(len(c['nodes']) for c in calls)
    independent={k:sum(layout(len(c['nodes']))[k] for c in calls) for k in layout(1)}
    independent['input_source_cells']=sum(16*c['message_bytes'] for c in calls)
    totals=dict(calls=sum(c['frequency'] for c in calls),unique_hash_inputs=len(calls),total_compression_calls=total,compression_calls_after_whole_input_dedup=whole_unique,unique_state_block_pairs=len(records),extra_compressions_removed_by_prefix_reuse=whole_unique-len(records),block_bytes_only_unique_INCORRECT_FOR_REUSE=len(naive_blockbytes))
    binary=b''.join(records);(out/'compression-records.bin').write_bytes(binary);(out/'hash-call-map.json').write_text(json.dumps(calls,separators=(',',':')))
    report=dict(status='PASS',totals=totals,lean_block_state_differential_checks=leanchecks,independent_direct_layout_after_whole_call_dedup=independent)
    report['shared_core_layout_estimates']=[dict(reuse=basis,**batched(count,chunk)) for basis,count in [('whole-hash-input',whole_unique),('exact-compression-state-block',len(records))] for chunk in (25,102)]
    report.update(source_proof_sha256=hashlib.sha256((src/'proof.json').read_bytes()).hexdigest(),source_statement_sha256=hashlib.sha256((src/'statement.json').read_bytes()).hexdigest(),records_sha256=hashlib.sha256(binary).hexdigest(),record_bytes=256,record_order='input state8 big-endian uint64,block128bytes,output state8 big-endian uint64',limits=['Trusted config setup excluded','Exact state+block equality measured; routing/fanout consistency still requires a new constrained AIR','Batched estimates preserve80 rounds per compression but omit new call/block/reset metadata and routing constraints','25-block chunks fit existing width5234/packing128/degree262144 limits;102-block chunks do not','Source cells are total work; peak raw chunk source bytes exclude JSON,auxiliary FFT/leaves/tree/GKR buffers','No recursive verifier coverage,zero-knowledge,proximity,QROM or128-bit security certification'])
    (out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
