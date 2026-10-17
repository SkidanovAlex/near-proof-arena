"""Lossless path-dictionary size experiment, not a new accepted proof profile.

Only existing path strings are replaced. No hashing, verification or algebra
is omitted. The rest remains canonical JSON; dictionary and framing are binary.
"""
import argparse,copy,json,struct
from pathlib import Path
MAGIC=b'NEAR-PATH-DICT-EXPERIMENT-1\0'
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def paths(x):
    if isinstance(x,dict):
        for k,v in x.items():
            if k=='path':yield x
            else:yield from paths(v)
    elif isinstance(x,list):
        for v in x:yield from paths(v)
def encode(proof):
    skeleton=copy.deepcopy(proof);dictionary=[];lookup={}
    for obj in paths(skeleton):
        ids=[]
        for digest in obj['path']:
            if type(digest)is not str or len(digest)!=96 or bytes.fromhex(digest).hex()!=digest:raise ValueError('digest')
            if digest not in lookup:lookup[digest]=len(dictionary);dictionary.append(digest)
            ids.append(lookup[digest])
        obj['path']=ids
    body=canonical(skeleton)
    return MAGIC+struct.pack('<IQ',len(dictionary),len(body))+b''.join(bytes.fromhex(h) for h in dictionary)+body
def decode(blob):
    if not blob.startswith(MAGIC) or len(blob)<len(MAGIC)+12:raise ValueError('header')
    n,size=struct.unpack('<IQ',blob[len(MAGIC):len(MAGIC)+12]);start=len(MAGIC)+12
    if len(blob)!=start+48*n+size:raise ValueError('length')
    dictionary=[blob[start+48*i:start+48*(i+1)].hex() for i in range(n)]
    if len(set(dictionary))!=n:raise ValueError('duplicate dictionary')
    body=blob[start+48*n:];proof=json.loads(body)
    if canonical(proof)!=body:raise ValueError('noncanonical JSON')
    for obj in paths(proof):
        if type(obj['path'])is not list or any(type(i)is not int or not 0<=i<n for i in obj['path']):raise ValueError('reference')
        obj['path']=[dictionary[i] for i in obj['path']]
    if encode(proof)!=blob:raise ValueError('noncanonical dictionary')
    return proof
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('proof',type=Path);ap.add_argument('--output-directory',type=Path,required=True);a=ap.parse_args()
    proof=json.loads(a.proof.read_bytes());raw=canonical(proof);wire=encode(proof)
    assert canonical(decode(wire))==raw
    nodes=[h for obj in paths(proof) for h in obj['path']]
    rejects=0
    for bad in (wire[:-1],wire+b'\0',b'X'+wire[1:]):
        try:decode(bad)
        except ValueError:rejects+=1
        else:raise AssertionError('malformed accepted')
    report=dict(status='PASS lossless encoding experiment',original_canonical_json_bytes=len(raw),encoded_bytes=len(wire),saved_bytes=len(raw)-len(wire),path_hash_occurrences=len(nodes),unique_path_hashes=len(set(nodes)),raw_path_hash_bytes=48*len(nodes),dictionary_hash_bytes=48*len(set(nodes)),roundtrip_exact=True,malformed_rejections=rejects,limits=['Not an accepted verifier wire profile; decoded object is byte-identical canonical proof.','Current Q8 Ext4 outer arithmetic proof only; required inner proofs/statements excluded.','Not a measured Ext8 high-query result or full recursive/PQ128 proof.'])
    a.output_directory.mkdir(parents=True,exist_ok=True);(a.output_directory/'proof.pathdict').write_bytes(wire);(a.output_directory/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
