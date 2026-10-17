#!/usr/bin/env python3
"""Executable full-state call-chain certificate; not commitment binding."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
from measure_sha384_block_dag import Probe
from check_sha384_occurrence_order import check as check_order

IV=bytes.fromhex('cbbb9d5dc1059ed8629a292a367cd5079159015a3070dd17152fecd8f70e593967332667ffc00b318eb44a8768581511db0c2e0d64f98fa747b5481dbefa4fa4')
PREFIX=b'NEAR-PQ384-PRIMITIVES-V1'


def frame(call):
    tag=call['tag'].encode('ascii');parts=[bytes.fromhex(p) for p in call['parts_hex']]
    return PREFIX+len(tag).to_bytes(4,'little')+tag+len(parts).to_bytes(4,'little')+b''.join(len(p).to_bytes(8,'little')+p for p in parts)


def validate(call,records,probe=None):
    message=frame(call)
    assert len(message)==call['message_bytes']
    padded=message+b'\x80'+b'\0'*((111-len(message))%128)+(8*len(message)).to_bytes(16,'big')
    ids=call['nodes'];assert len(ids)*128==len(padded) and ids
    state=IV
    for step,node in enumerate(ids):
        assert type(node) is int and 0<=node<len(records)
        record=records[node];assert len(record)==256
        assert record[:64]==state
        assert record[64:192]==padded[128*step:128*(step+1)]
        state=record[192:256] # all512bits, never truncated between blocks
    assert state[:48].hex()==call['digest_hex']
    assert state[:48]==hashlib.sha384(message).digest()
    if probe is not None:
        independently_padded,states=probe.run(message)
        assert independently_padded==padded
        for step,node in enumerate(ids):
            assert records[node][:64]==struct.pack('>8Q',*states[step])
            assert records[node][192:]==struct.pack('>8Q',*states[step+1])
    return {'message_bytes':len(message),'blocks':len(ids),'final_state_hex':state.hex(),
            'digest_hex':state[:48].hex(),'message_sha256':hashlib.sha256(message).hexdigest()}


def main():
    p=argparse.ArgumentParser();p.add_argument('--dag-directory',type=Path,required=True)
    p.add_argument('--occurrence-directory',type=Path,required=True)
    p.add_argument('--probe-library',type=Path,required=True);p.add_argument('--output-directory',type=Path,required=True)
    a=p.parse_args();d=a.dag_directory;o=a.occurrence_directory
    paths=[d/'hash-call-map.json',d/'compression-records.bin',o/'occurrence-call-ids.json',o/'ordered-occurrence-uses.json']
    calls=json.loads(paths[0].read_text());raw=paths[1].read_bytes();assert len(raw)%256==0
    records=[raw[i:i+256] for i in range(0,len(raw),256)]
    events=json.loads(paths[2].read_text());uses=json.loads(paths[3].read_text())
    check_order(calls,events,uses)
    probe=Probe(str(a.probe_library))
    certificates=[validate(c,records,probe) for c in calls]
    occurrence_certificates=[];cursor=0
    for ordinal,index in enumerate(events):
        cert=certificates[index];count=cert['blocks']
        assert uses[cursor:cursor+count]==[[ordinal,index,j,node] for j,node in enumerate(calls[index]['nodes'])]
        occurrence_certificates.append({'ordinal':ordinal,'unique_call':index,'use_start':cursor,'use_count':count})
        cursor+=count
    assert cursor==len(uses)
    negatives=[]
    # Representative complete three-block call; mutation checks need no re-execution.
    call=next(c for c in calls if len(c['nodes'])==3)
    def reject(name,c,rs):
        try:validate(c,rs)
        except (AssertionError,IndexError):negatives.append(name)
        else:raise AssertionError('accepted '+name)
    for step,offset,name in [(0,0,'nonstandard IV'),(0,64,'message byte'),(2,191,'encoded padding length'),(1,0,'chaining input'),(0,248,'hidden chaining output'),(2,192,'terminal digest')]:
        changed=list(records);node=call['nodes'][step];r=bytearray(changed[node]);r[offset]^=1;changed[node]=bytes(r)
        reject(name,call,changed)
    for name,ids in [('omitted block',call['nodes'][:-1]),('reordered blocks',list(reversed(call['nodes']))),('duplicate block',[call['nodes'][0]]*3)]:
        reject(name,dict(call,nodes=ids),records)
    reject('wrong declared length',dict(call,message_bytes=call['message_bytes']+1),records)
    reject('wrong final digest',dict(call,digest_hex='00'*48),records)
    out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    certpath=out/'call-chain-certificates.json';occpath=out/'occurrence-chain-map.json'
    certpath.write_text(json.dumps(certificates,separators=(',',':'))+'\n')
    occpath.write_text(json.dumps(occurrence_certificates,separators=(',',':'))+'\n')
    paths += [a.probe_library,Path(__file__),Path(__file__).with_name('measure_sha384_block_dag.py'),Path(__file__).with_name('check_sha384_occurrence_order.py'),certpath,occpath]
    report={'status':'PASS','unique_calls':len(calls),'actual_occurrences':len(events),'actual_steps':cursor,
      'full_state_bits':512,'digest_bytes':48,'negative_cases':negatives,
      'files':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths],
      'scope':['Every unique call checked against canonical framing/padding, standard IV, full-state links, final digest and independent OpenSSL compression states.',
       'Every observed chronological occurrence maps to its complete ordered block path; no deduplication of occurrence ordinals.',
       'Replay provenance supplies chronology; this certificate alone does not authenticate event order.',
       'No new proof, commitment binding, recursive-verifier proof, or quantum security claim.']}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('files','scope')}))

if __name__=='__main__':main()
