"""Replay the actual compiler's coefficient accumulation through proved Lean code."""
import argparse,gzip,hashlib,json,subprocess
from pathlib import Path
import sha384_call_pcs as cp
from pq384_primitives import Transcript,hash_parts


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    source=package/'results/ext8-linked-calls';read=lambda f:json.loads(f.read_text())
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));calls=read(source/'calls.json')
    receipt=read(package/'results/ext8-node-batch/expected-use.json');capacity=(1<<st['spec']['log_rows'][3])*256
    eq=cp.equations(st,receipt,calls)
    seed=hash_parts(cp.PROFILE,cp.canonical(receipt),cp.canonical(calls),cp.canonical(st['spec']),bytes.fromhex(st['roots'][3]))
    point=[tuple(x) for x in Transcript(seed).draw(b'call-equations-after-use-root',(len(eq)-1).bit_length(),4)[0]]
    all_weights=cp.g.eqs(point)
    weights=all_weights[:len(eq)]
    padded=eq+[(0,0,0)]*(len(all_weights)-len(eq))
    assert cp.compile_coefficients(eq,weights,capacity)==cp.compile_coefficients(padded,all_weights,capacity)
    scenarios=[('retained',eq,weights,capacity),('padded',padded,all_weights,capacity),('aliases',[(0,0,0),(1,None,7),(1,1,0),(0,1,3),(1,None,2)],
        [cp.g.ZERO,cp.g.ONE,(2,3,4,5),(6,7,8,9),cp.g.ONE],2)]
    reports=[];certificates=[]
    scenarios.append(('zero-support',[(0,0,0)],[cp.g.ONE],2))
    scenarios.append(('constant-failure',[(0,None,1),(0,None,2)],[cp.g.ONE,cp.g.sub(cp.g.ZERO,cp.g.ONE)],2))
    for name,eqs,ws,cap in scenarios:
        fixture=out/(name+'.json');output=out/(name+'-lean.json')
        fixture.write_text(json.dumps(dict(capacity=cap,equations=[[l,int(r is not None),r or 0,v] for l,r,v in eqs],weights=ws)))
        run=subprocess.run(['lake','env','lean','--run','ReplayCallArray.lean',str(fixture),str(output)],cwd=package,text=True,capture_output=True)
        (out/(name+'.log')).write_text(run.stdout+run.stderr);run.check_returncode()
        result=read(output);coeff,claim=cp.compile_coefficients(eqs,ws,cap)
        assert len(result)==4
        assert all(result[k][0]==[c[k] for c in coeff] and result[k][1]==claim[k] for k in range(4))
        dag=cp.compile_dag(coeff,claim,cap)
        def structural(candidate):
            nodes=candidate['nodes'];root=candidate['root'];active=[i for i,c in enumerate(coeff) if c!=cp.g.ZERO]
            assert nodes[:cap]==[['input',i] for i in range(cap)]
            for i,node in enumerate(nodes):
                if node[0] in ('add','sub','mul'):assert all(0<=j<i for j in node[1:])
            assert nodes[root][0]=='sub'
            total,constant=nodes[root][1:];assert nodes[constant]==['const',*claim]
            def leaves(i):
                node=nodes[i]
                if node[0]=='add':return leaves(node[1])+leaves(node[2])
                if node==['const',*cp.g.ZERO]:return []
                assert node[0]=='mul'
                slot,c=node[1:];assert 0<=slot<cap and coeff[slot]!=cp.g.ZERO
                assert nodes[slot]==['input',slot] and nodes[c]==['const',*coeff[slot]]
                return [slot]
            assert leaves(total)==active
        structural(dag)
        constant_nodes=[0]*cap;product_nodes=[0]*cap
        for i,node in enumerate(dag['nodes']):
            if node[0]=='mul':
                slot,c=node[1:];constant_nodes[slot]=c;product_nodes[slot]=i
        current=[product_nodes[i] for i,c in enumerate(coeff) if c!=cp.g.ZERO]
        stages=[[[i,True] for i in current]]
        additions={(node[1],node[2]):i for i,node in enumerate(dag['nodes']) if node[0]=='add'}
        while len(current)>1:
            current=[additions[current[i],current[i+1]] if i+1<len(current) else current[i] for i in range(0,len(current),2)]
            stages.append([[i,True] for i in current])
        total,claim_node=dag['nodes'][dag['root']][1:]
        certificate=dict(nodes=dag['nodes'],coefficients=coeff,claim=claim,capacity=cap,
            constants=constant_nodes,products=product_nodes,balance=dict(stages=stages,result=total),
            root=dag['root'],claim_node=claim_node,expected=True)
        certificates.append(certificate)
        if name=='retained':
            for mutation in ('root','constant','product','support'):
                bad=json.loads(json.dumps(certificate));bad['expected']=False
                first=next(i for i,c in enumerate(coeff) if c!=cp.g.ZERO)
                if mutation=='root':bad['nodes'][bad['root']][0]='add'
                elif mutation=='constant':bad['nodes'][constant_nodes[first]][1]=(bad['nodes'][constant_nodes[first]][1]+1)%cp.P
                elif mutation=='product':bad['nodes'][product_nodes[first]][0]='add'
                else:bad['products'][first]=0
                certificates.append(bad)
        bad=json.loads(json.dumps(dag));bad['nodes'][bad['root']][0]='add'
        try:structural(bad)
        except AssertionError:pass
        else:raise AssertionError('wrong root accepted')
        layout=cp.g.layer_circuit(dag)
        for mode in range(3):
            private=[cp.g.ZERO if mode==0 else tuple((i*(j+3)+mode+j)%cp.P for j in range(4)) for i in range(cap)]
            nodevalues=[]
            for node in dag['nodes']:
                if node[0]=='input':value=private[node[1]]
                elif node[0]=='const':value=tuple(node[1:])
                else:value=cp.g.gate(node[0],nodevalues[node[1]],nodevalues[node[2]])
                nodevalues.append(value)
            dot=cp.g.ZERO
            for c,x in zip(coeff,private):dot=cp.g.add(dot,cp.g.mul(c,x))
            target=cp.g.sub(dot,claim)
            assert nodevalues[dag['root']]==target==cp.g.values(layout,private)[-1][layout['root']]
        reports.append(dict(name=name,dag_nodes=len(dag['nodes']),structural_route_checked=True,dag_and_layer_evaluations_match=True,wrong_root_rejected=True,equations=len(eqs),capacity=cap,all_coefficients_and_claim_match=True,
            replay_sha256=hashlib.sha256(output.read_bytes()).hexdigest()))
    certificate_file=out/'circuits.json';certificate_file.write_text(json.dumps(certificates,separators=(',',':')))
    checked=subprocess.run(['lake','env','lean','--run','CheckCallCircuit.lean',str(certificate_file)],cwd=package,text=True,capture_output=True)
    (out/'circuit-check.log').write_text(checked.stdout+checked.stderr);checked.check_returncode()
    # The compiler refactor must preserve the existing proof and its exact wire encoding.
    proofdir=package/'results/ext8-call-pcs'
    proof=json.loads(gzip.decompress((proofdir/'proof.json.gz').read_bytes()))
    wire=(proofdir/'proof.bin').read_bytes()
    assert cp.encode(proof,st,receipt,calls)==wire
    report=dict(status='PASS',scenarios=reports,lean_circuit_certificates_accepted=5,lean_circuit_mutations_rejected=4,padded_and_unpadded_compilation_identical=True,retained_proof_verifies_and_encoding_unchanged=True,
        proof_sha256=hashlib.sha256(wire).hexdigest(),
        scope='Concrete array parity and structural sparse-DAG checks, with three input vectors per DAG/layer comparison, aliases and empty support. General Lean DAG-to-functional theorem requires an acyclic structural route. Extracted DAG certificates also pass the proved Lean checker, with four mutations rejected; actual layered certificate replay, Fiat-Shamir/QROM soundness and full recursion remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
