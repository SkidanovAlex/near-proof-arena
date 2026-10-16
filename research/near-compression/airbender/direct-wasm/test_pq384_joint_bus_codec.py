import argparse,copy,json,os,subprocess,sys,time,struct
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--input-directory',required=True)
    p.add_argument('--output-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_joint_bus_codec as codec
    import pq384_joint_codec as opening
    inp=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    proof=json.loads((inp/'proof.json').read_text());trusted=json.loads((inp/'statement.json').read_text());spec=trusted['spec'];roots=[bytes.fromhex(v) for v in trusted['roots']]
    start=time.perf_counter();data=codec.encode(proof,spec,roots);assert codec.decode(data,spec,roots)==proof
    assert codec.verify_shared(data,spec,roots)
    (out/'proof.bin').write_bytes(data);env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    checked=subprocess.run([sys.executable,str(Path(codec.__file__)),str(out/'proof.bin'),str(inp/'statement.json')],env=env,check=True,capture_output=True,text=True)
    rejects=0
    def reject(b,s=spec,rs=roots):
        nonlocal rejects
        try:codec.decode(b,s,rs)
        except (ValueError,KeyError,TypeError,IndexError):rejects+=1
        else:raise AssertionError('joint malformed input accepted')
        try:codec.verify_shared(b,s,rs)
        except (ValueError,KeyError,TypeError,IndexError):pass
        else:raise AssertionError('joint shared verifier accepted malformed input')
    fixed,minimum,maximum=codec.shape(spec)
    for bad in [data[:-1],data+b'\0',b'X'+data[1:],bytes(fixed+8+maximum+1)]:reject(bad)
    for offset in [len(codec.MAGIC),fixed-16,fixed+8+len(opening.MAGIC),len(data)//2,len(data)-1]:
        bad=bytearray(data);bad[offset]^=1;reject(bytes(bad))
    bad=bytearray(data);bad[fixed:fixed+8]=struct.pack('<Q',2**64-1);reject(bytes(bad))
    args=codec.combined.arguments(proof['air'],spec,roots);metadata=opening.stages(proof['joint'],args)
    source_leaves=source_siblings=fold_leaves=fold_siblings=0
    for j,(_,_,count,indices,w) in enumerate(metadata):
        leaf=len(set(indices))*4*w;sibling=len(opening.mp.boundary(count,indices))*48
        if j<len(args):source_leaves+=leaf;source_siblings+=sibling
        else:fold_leaves+=leaf;fold_siblings+=sibling
    _,header,_=opening.limits(args)
    assert len(data)==fixed+8+header+source_leaves+source_siblings+fold_leaves+fold_siblings
    offset=fixed+8+header
    for _,_,count,indices,w in metadata:
        leaf_bytes=len(set(indices))*4*w;sibling_bytes=len(opening.mp.boundary(count,indices))*48
        for at,size in [(offset,leaf_bytes),(offset+leaf_bytes,sibling_bytes)]:
            if size:
                bad=bytearray(data);bad[at]^=1;reject(bytes(bad))
        offset+=leaf_bytes+sibling_bytes
    assert offset==len(data)
    wrong=copy.deepcopy(spec);wrong['public'][0]^=1;reject(data,wrong)
    wrongroots=list(roots);wrongroots[0]=bytes([roots[0][0]^1])+roots[0][1:];reject(data,spec,wrongroots)
    report=dict(status='PASS',whole_proof_bytes=len(data),retained_air_roots_finals_claims=fixed,joint_length_frame=8,
        joint_header_reduction_rounds_terminal=header,initial_source_leaves=source_leaves,initial_source_siblings=source_siblings,
        shared_fold_leaves=fold_leaves,shared_fold_siblings=fold_siblings,negative_checks=rejects,
        exact_roundtrip=True,shared_verification=True,shared_rejections=rejects,
        verification=checked.stdout.strip(),test_seconds=time.perf_counter()-start,
        scope='Full actual workload size; new joint PCS soundness not established')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
