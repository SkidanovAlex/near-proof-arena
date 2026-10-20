"""Actual two-call selection and canonical-chain witness projection; no synthetic hash rows."""
import argparse,collections,hashlib,json,struct
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--call-map',required=True);p.add_argument('--selection',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--chain-directories',nargs=2);a=p.parse_args()
    out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);calls=json.loads(Path(a.call_map).read_text());sel=json.loads(Path(a.selection).read_text());chosen=[calls[i] for i in sel['actual_call_map_indices']];assert len(chosen)==2 and sel['call_paths']==[[0,1,2],[0,3,4]]
    messages=[];fixeds=[]
    for c,call in enumerate(chosen):
        msg=bytearray();fixed=[]
        def const(data):
            start=len(msg);msg.extend(data);fixed.extend([start+i,v] for i,v in enumerate(data))
        tag=call['tag'].encode();parts=[bytes.fromhex(x) for x in call['parts_hex']]
        const(b'NEAR-PQ384-PRIMITIVES-V1');const(struct.pack('<I',len(tag)));const(tag);const(struct.pack('<I',len(parts)))
        for part in parts:const(struct.pack('<Q',len(part)));msg.extend(part)
        assert len(msg)==267 and hashlib.sha384(msg).hexdigest()==call['digest_hex'];messages.append(bytes(msg));fixeds.append(fixed)
        (out/f'message-{c}.bin').write_bytes(msg);(out/f'fixed-{c}.json').write_text(json.dumps(fixed,separators=(',',':')))
    (out/'selection.json').write_text(json.dumps(sel,indent=2))
    if not a.chain_directories:return
    spec=json.loads((out/'spec.json').read_text());assert spec['public']==list(b''.join(hashlib.sha384(m).digest() for m in messages))
    nodes={};provenance=[]
    for c,path in enumerate(a.chain_directories):
        base=Path(path);report=json.loads((base/'chain.json').read_text());msg=messages[c];padded=msg+b'\x80'+bytes((111-len(msg))%128)+(8*len(msg)).to_bytes(16,'big')
        assert report['message_bytes']==list(msg) and report['padded_bytes']==list(padded) and report['digest_bytes']==list(hashlib.sha384(msg).digest()) and report['block_count']==3 and report['chain_boundary_check']
        for b,node in enumerate(sel['call_paths'][c]):
            raw=(base/f'block-{b}'/'source-00-rows.json').read_bytes();rows=json.loads(raw)['rows'];assert len(rows)==128 and all(len(r)==6944 for r in rows)
            if node in nodes:assert nodes[node]==rows,'shared full-state block must reproduce exact canonical witness'
            else:nodes[node]=rows
            provenance.append(dict(call=c,block=b,node=node,sha256=hashlib.sha256(raw).hexdigest()))
    core=[];endpoint=[];records=[];counts=collections.Counter(i for path in sel['call_paths'] for i in path)
    for node in range(5):
        rows=nodes[node];ep=rows[79][5280:];assert len(ep)==1664
        for phase,row in enumerate(rows[:80]):
            assert row[5152:5280]==[int(i==phase) for i in range(128)];core.append(row[:5232]+[1,node])
        endpoint.append(ep+[node,1]);A=[ep[208*w+l] for w in range(8) for l in range(4)];M=[sum(rows[0][[1440,576,1776,1840,1904,1968,2032,2096,2160,1232,2224,2288,2352,2416,0,2480][w]+16*l+j]*(1<<j) for j in range(16)) for w in range(16) for l in range(4)]
        # Exact sha512ScheduleWindowBase mapping from canonical combined source.
        C=[ep[208*w+8+l] for w in range(8) for l in range(4)]
        D=list(b''.join(sum(C[4*w+l]<<(16*l) for l in range(4)).to_bytes(8,'big') for w in range(6)))
        records.append([node,1,counts[node]&1,(counts[node]>>1)&1]+A+M+C+D)
    steps=[]
    for c,path in enumerate(sel['call_paths']):
        for phase,node in enumerate(path):steps.append([c,node,1]+[int(i==phase) for i in range(3)]+records[node][4:])
    traces=[core,endpoint,records,steps]+[[[(v>>i)&1 for v in m for i in range(8)],[0]*2136] for m in messages]
    for t,(trace,log,table) in enumerate(zip(traces,spec['log_rows'],spec['air']['tables'])):
        while len(trace)<1<<log:trace.append([0]*table['width'])
        assert len(trace)==1<<log and all(len(row)==table['width'] for row in trace)
        (out/f'source-{t:02d}-rows.json').write_text(json.dumps({'rows':trace},separators=(',',':')))
    report=dict(status='PASS',actual_call_indices=sel['actual_call_map_indices'],logical_blocks=6,unique_compressions=5,call_paths=sel['call_paths'],natural_fanout=[counts[i] for i in range(5)],source_shapes=[[len(tr),len(tr[0])] for tr in traces],source_cells=sum(len(tr)*len(tr[0]) for tr in traces),padded_core_rows=512,independent_two_call_padded_core_rows=512,padded_core_row_savings=0,source_block_provenance=provenance,call_map_sha256=hashlib.sha256(Path(a.call_map).read_bytes()).hexdigest(),scope='Actual canonical Lean compression witnesses projected into new shared-node AIR; no security or complete recursion claim.')
    (out/'preparation-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
