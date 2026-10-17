"""Experimental GKR-specific transcript; a new protocol, not v2 equivalence.

One pending commit per draw; explicit profile, labels, round and retry counters.
Existing rejection rule is retained. No QROM/composition theorem is asserted.
"""
import importlib.util,json,struct
from pathlib import Path
import pq384_primitives as p
PROFILE=b'nearproof-fused-terminal-gkr-v3'

class FusedTranscript:
    def __init__(self,layout,statement,claim,g):
        self.inputs={'statement':statement,'claim':g.vector_bytes([g.ext(claim)])}
        self.nodes=[];self.digests=[];self.draws=[];self.pending=None;self.round=0
        digest=p.hash_parts(PROFILE,json.dumps(layout,sort_keys=True,separators=(',',':')).encode())
        self.seed=self.hp(PROFILE,[['input','statement'],['literal',digest.hex()],['input','claim']])
    def resolve(self,ref):
        kind,value=ref
        if kind=='literal':return bytes.fromhex(value)
        if kind=='input':return self.inputs[value]
        if kind=='hash' and type(value)is int and 0<=value<len(self.digests):return self.digests[value]
        raise ValueError('invalid hash reference')
    def hp(self,tag,refs):
        parts=[self.resolve(r) for r in refs]
        wire=p.PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(p.u64(len(x))+x for x in parts)
        digest=p.hash_parts(tag,*parts)
        self.nodes.append(dict(tag=tag.decode(),parts=refs,digest=digest.hex(),blocks=(len(wire)+144)//128))
        self.digests.append(digest);return ['hash',len(self.nodes)-1]
    def commit(self,label,payload):
        p.require(self.pending is None and label==b'gkr-vector' and type(payload)is bytes,'commit schedule')
        self.pending=(label,payload)
    def draw(self,label,count,coefficients,max_blocks=4096):
        p.require(self.pending is not None and label==b'gkr-challenge' and type(count)is int and type(coefficients)is int and count==1 and coefficients==4,'draw schedule')
        p.require(type(max_blocks)is int and 0<max_blocks<=1<<20,'draw budget')
        start=len(self.nodes);name=f'proof/{self.round}';commit_label,payload=self.pending
        self.inputs[name]=payload;values=[];rejected=0;scans=[]
        literal=lambda b:['literal',b.hex()]
        for counter in range(max_blocks):
            block=self.hp(b'transcript/squeeze',[literal(PROFILE),self.seed,literal(commit_label),['input',name],
                literal(label),literal(p.u64(self.round)),literal(p.u64(count)),literal(p.u64(coefficients)),literal(p.u64(counter))])
            words=p.digest_words(self.resolve(block));accepted=[];bad=0
            for word in words:
                value=p.accept_word(word)
                if value is None:bad+=1
                else:
                    values.append(value);accepted.append(value)
                    if len(values)==4:break
            rejected+=bad;scans.append(dict(hash_node=block[1],words=words,accepted=accepted,rejected=bad))
            if len(values)==4:
                self.seed=block;self.pending=None;self.round+=1
                self.draws.append(dict(input=name,scans=scans,values=values,blocks=counter+1,next_seed=block[1]))
                return [values],dict(blocks=counter+1,rejected_words=rejected)
        del self.nodes[start:];del self.digests[start:];del self.inputs[name]
        raise ValueError('rejection sampler exhausted block budget')
    def graph(self):
        return dict(inputs={k:v.hex() for k,v in self.inputs.items()},nodes=self.nodes,draws=self.draws)

def candidate():
    path=Path(__file__).with_name('pq384_terminal_gkr.py')
    spec=importlib.util.spec_from_file_location('fused_terminal_gkr_candidate',path)
    g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
    g.PROFILE=PROFILE;g.last_transcript=None
    def begin(layout,statement,claim):
        t=FusedTranscript(layout,statement,claim,g);g.last_transcript=t;return t
    g.begin=begin
    return g
