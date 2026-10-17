"""Packed RS encoding cross-checks and first-opening cost measurements.

Not a PCS proof-size benchmark: no proximity proof or terminal claim removal.
"""
import json
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from pq384_primitives import P, field_words, merkle_tree, verify_path, u64
from test_pq384_rs import evaluate


def context(n, width, packing, omega):
    lanes = (width+packing-1)//packing
    return (b'NEAR-PQ384-RS-PACKED-V2/row-low-column-high-mobius/'
            b'consecutive-column-groups/zero-pad-columns-and-lde4/'
            b'natural-domain/lane-major-pairs/le-u32'
            + b''.join(u64(v) for v in (P,n,width,packing,lanes,4*n*packing,omega)))


def eval_packed(rows, packing, x):
    # First evaluate each source column, then interpolate column groups.
    # No packed coefficient construction or FFT is shared with native code.
    values = evaluate(rows,x)
    point = pow(x,len(rows),P)
    out = []
    for start in range(0,len(values),packing):
        group = values[start:start+packing]
        group += [0]*(packing-len(group))
        out.append(evaluate([[v] for v in group],point)[0])
    return out


def pair(rows, packing, omega, index):
    x = pow(omega,index,P)
    return [v for ab in zip(eval_packed(rows,packing,x),
                            eval_packed(rows,packing,(-x)%P)) for v in ab]


def run(binary, rows, packing, full):
    n,width=len(rows),len(rows[0]);lanes=(width+packing-1)//packing
    half=2*n*packing;omega=pow(440564289,(1<<27)//(2*half),P)
    indices=list(range(half)) if full else [0,13,half-1]
    ctx=context(n,width,packing,omega)
    with tempfile.TemporaryDirectory(prefix='near-pq384-pack-') as d:
        src,dst=Path(d)/'input.json',Path(d)/'output.json'
        src.write_text(json.dumps({'rows':rows,'indices':indices,'packing':packing}))
        start=time.monotonic()
        subprocess.run([binary,str(src),str(dst)],check=True,capture_output=True)
        elapsed=time.monotonic()-start;out=json.loads(dst.read_text())
    assert (out['profile'],out['rows'],out['width'],out['packing'],out['lanes']) == (
        'near-pq384-rs-packed-v2',n,width,packing,lanes)
    assert out['domain_size']==2*half and out['omega']==omega
    assert bytes.fromhex(out['context_hex'])==ctx
    root=struct.pack('<12I',*out['root'])
    assert [o['index'] for o in out['openings']]==indices
    payloads=[];negatives=0
    for o in out['openings']:
        i=o['index'];expected=pair(rows,packing,omega,i)
        assert o['leaf']==expected, ('packed RS mismatch',packing,i)
        leaf=field_words(expected);payloads.append(leaf)
        path=[struct.pack('<12I',*h) for h in o['path']]
        assert verify_path(root,ctx,half,i,leaf,path)
        altered=expected.copy();altered[0]=(altered[0]+1)%P
        for badctx,badleaf in [(ctx,field_words(altered)),
                               (context(n,width+1,packing,omega),leaf),
                               (context(n,width,packing*2,omega),leaf)]:
            try:verify_path(root,badctx,half,i,badleaf,path)
            except ValueError:negatives+=1
            else:raise AssertionError('accepted changed packing/opening')
    if full:assert merkle_tree(payloads,ctx)[0]==root
    query_bytes=len(payloads[0])+48*(half.bit_length()-1)
    return {'rows':n,'width':width,'packing':packing,'lanes':lanes,
            'padded_width':lanes*packing,'root_hex':root.hex(),'sampled_pairs':len(indices),
            'full_root_reconstruction':full,'negative_checks':negatives,
            'first_opening_leaf_and_path_bytes':query_bytes,
            'native_seconds_including_io':elapsed}


def main():
    binary,source,report=sys.argv[1:]
    rows=json.loads(Path(source).read_text())['rows']
    small=[[((i+1)*(j+3)*739+P-1)%P for j in range(7)] for i in range(4)]
    cases=[run(binary,small,p,True) for p in (1,2,8)]
    cases += [run(binary,rows,p,False) for p in (1,8,32,128)]
    result={'status':'PASS','cases':cases,
            'scope':'SHA384 packed RS encoding; opening bytes exclude framing/root and are NOT complete proof sizes',
            'reference':'Direct row MLE then column MLE; independent of native Mobius and FFT',
            'limits':['Three full vector pairs checked per large case; not full independent root reconstruction',
                      'Single-run shared-host timings; no peak memory measurement',
                      'Terminal column claims retained; no PCS integration or quantum security claim']}
    Path(report).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
