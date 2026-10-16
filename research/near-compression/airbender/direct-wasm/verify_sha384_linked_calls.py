"""Diagnostic compression proof + disclosed committed uses + trusted hash calls.

Call messages, ordered ordinals and expected digests are external configuration,
not selected by the proof. This discloses the entire small use table; it is not
succinct recursive authentication or a quantum-security certification.
"""
import argparse,json,subprocess,tempfile
from pathlib import Path
from pq384_primitives import P,require,field_words,merkle_tree
from packed_claim_handoff import packing_context
from verify_sha384_node_chunk import contract,verify as verify_compressions


def reconstructed_use_root(rows,log_rows,packing):
    context=packing_context(log_rows,179,packing)
    require(len(rows)==1<<log_rows and all(len(r)==179 for r in rows),'use rows shape')
    require(all(type(x)is int and 0<=x<P for r in rows for x in r),'canonical use fields')
    degree=len(rows)*packing;require(degree<=262144,'bounded disclosed use degree')
    domain=4*degree;omega=pow(440564289,(1<<27)//domain,P);encoded=[]
    for start in range(0,179,packing):
        c=[row[col] if col<179 else 0 for col in range(start,start+packing) for row in rows]
        bit=1
        while bit<degree:
            for i in range(degree):
                if i&bit:c[i]=(c[i]-c[i^bit])%P
            bit*=2
        v=c+[0]*(domain-degree);j=0
        for i in range(1,domain):
            bit=domain>>1
            while j&bit:j^=bit;bit>>=1
            j^=bit
            if i<j:v[i],v[j]=v[j],v[i]
        size=2
        while size<=domain:
            step=pow(omega,domain//size,P)
            for start_at in range(0,domain,size):
                power=1
                for i in range(start_at,start_at+size//2):
                    u=v[i];b=v[i+size//2]*power%P
                    v[i]=(u+b)%P;v[i+size//2]=(u-b)%P;power=power*step%P
            size*=2
        encoded.append(v)
    half=domain//2
    leaves=[field_words([x for lane in encoded for x in (lane[i],lane[i+half])]) for i in range(half)]
    return merkle_tree(leaves,context)[0].hex()


def linked_cases(statement,expected,rows,calls):
    contract(statement,expected)
    spec=statement['spec'];uses=expected['use_count']
    require(reconstructed_use_root(rows,spec['log_rows'][3],spec['source_packings'][3])==expected['use_root'],'disclosed uses must match fixed proof root')
    require(type(calls)is list and calls,'external calls required')
    cases=[];coverage=[]
    for call in calls:
        require(type(call)is dict and set(call)=={'message_hex','ordinals','digest_hex'},'external call fields')
        message=bytes.fromhex(call['message_hex']);digest=bytes.fromhex(call['digest_hex']);ids=call['ordinals']
        require(len(digest)==48 and type(ids)is list and ids and all(type(i)is int and 0<=i<uses for i in ids),'call digest/ordinals')
        padded=message+b'\x80'+b'\0'*((111-len(message))%128)+(8*len(message)).to_bytes(16,'big')
        require(len(padded)==128*len(ids),'call block count')
        final=[sum(rows[ids[-1]][99+4*w+j]<<(16*j) for j in range(4)) for w in range(8)]
        require(all(x<2**64 for x in final),'canonical final state')
        require(b''.join(x.to_bytes(8,'big') for x in final)[:48]==digest,'external expected digest')
        cases.append(dict(name=f'call-{len(cases)}',rows=rows[:uses],message=list(message),ordinals=ids,
            blocks=[list(padded[i:i+128]) for i in range(0,len(padded),128)],final=final,expected=True))
        coverage.extend(ids)
    require(coverage==list(range(uses)),'exact ordered call coverage')
    return cases


def verify(wire,statement,expected,rows,calls,package):
    cases=linked_cases(statement,expected,rows,calls)
    with tempfile.TemporaryDirectory(prefix='linked-sha384-calls-') as tmp:
        fixture=Path(tmp)/'calls.json';fixture.write_text(json.dumps(cases,separators=(',',':')))
        result=subprocess.run(['lake','env','lean','--run','CheckSHA384ChunkCalls.lean',str(fixture)],cwd=package,text=True,capture_output=True,check=True)
        require(json.loads(result.stdout.strip().splitlines()[-1])==dict(status='PASS',accepted=len(calls),rejected=0),'all Lean call checks required')
    verify_compressions(wire,statement,expected)
    return True


def main():
    p=argparse.ArgumentParser()
    for name in ['proof','statement','receipt','rows','calls','package']:p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();read=lambda f:json.loads(f.read_text())
    verify(a.proof.read_bytes(),read(a.statement),read(a.receipt),read(a.rows),read(a.calls),a.package)
    print('PASS linked disclosed-call diagnostic; Q8/Ext4, no recursive or quantum-security claim.')

if __name__=='__main__':main()
