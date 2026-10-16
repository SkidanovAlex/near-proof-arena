"""Independent scalar oracle and native SHA384 check of the terminal rule."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
from pq384_terminal import verify_terminal, terminal_context

P=2013265921


def product(a,b):
    # Direct quotient-ring convolution, independent of verifier Horner.
    out=[0]*4
    for i in range(4):
        for j in range(4):out[(i+j)%4]=(out[(i+j)%4]+a[i]*b[j]*(11 if i+j>=4 else 1))%P
    return out


def plus(a,b):return [(x+y)%P for x,y in zip(a,b)]


def power_sum(coeffs,x):
    return [sum(c[k]*pow(x,i,P) for i,c in enumerate(coeffs))%P for k in range(4)]


def sample(label,i,j,k):
    return int.from_bytes(hashlib.sha384(f'{label}/{i}/{j}/{k}'.encode()).digest(),'little')%P


def run(binary,degree,domain,lanes):
    coefficients=[[[sample('coeff',i,j,k) for k in range(4)] for j in range(degree)] for i in range(lanes)]
    weights=[[[sample('weight',i,j,k) for k in range(4)] for j in range(degree)] for i in range(lanes)]
    stage=b'fixture/round3/terminal';context,omega=terminal_context(stage,degree,domain,lanes)
    leaves=[]
    for i in range(domain//2):
        x=pow(omega,i,P)
        leaves.append([v for cs in coefficients for y in (x,(-x)%P) for v in power_sum(cs,y)])
    with tempfile.TemporaryDirectory(prefix='near-terminal-') as d:
        src,dst=Path(d)/'input.json',Path(d)/'output.json'
        src.write_text(json.dumps({'statement_hex':'','events':[],
                                  'context_hex':context.hex(),'leaves':leaves}))
        subprocess.run([binary,str(src),str(dst)],check=True,capture_output=True)
        root=struct.pack('<12I',*json.loads(dst.read_text())['root'])
    claim=[0]*4
    for cs,ws in zip(coefficients,weights):
        for c,w in zip(cs,ws):claim=plus(claim,product(c,w))
    proof={'profile':'near-pq384-terminal-v1','coefficients':coefficients}
    args=dict(expected_root=root,stage_binding=stage,degree_bound=degree,
              domain_size=domain,lanes=lanes,weights=weights,claim=claim)
    assert verify_terminal(proof,**args)
    rejected=0
    def reject(p,a):
        nonlocal rejected
        try:verify_terminal(p,**a)
        except ValueError:rejected+=1
        else:raise AssertionError('invalid terminal accepted')
    for i in range(lanes):
        for j in range(degree):
            for k in range(4):
                bad=copy.deepcopy(proof);bad['coefficients'][i][j][k]=(bad['coefficients'][i][j][k]+1)%P
                reject(bad,args)
    for key,value in [('profile','old'),('extra',0),('coefficients',coefficients[:-1])]:
        bad=copy.deepcopy(proof);bad[key]=value;reject(bad,args)
    for value in [[],coefficients[0]+[[0]*4]]:
        bad=copy.deepcopy(proof);bad['coefficients'][0]=value;reject(bad,args)
    for value in [P,-1,True]:
        bad=copy.deepcopy(proof);bad['coefficients'][0][0][0]=value;reject(bad,args)
    bad=copy.deepcopy(proof);bad['coefficients'][0][0]=[0]*3;reject(bad,args)
    for key,value in [('expected_root',root[:-1]),('stage_binding',stage+b'x'),
                      ('degree_bound',degree+1),('domain_size',2),('domain_size',3),('lanes',lanes+1),
                      ('weights',weights[:-1]),('claim',[(claim[0]+1)%P]+claim[1:])]:
        bad=copy.deepcopy(args);bad[key]=value;reject(proof,bad)
    bad=copy.deepcopy(args);bad['expected_root']=bytes([root[0]^1])+root[1:];reject(proof,bad)
    # Correct authenticated polynomial, but wrong externally supplied residual.
    bad=copy.deepcopy(args);bad['weights'][0][0][0]=(bad['weights'][0][0][0]+1)%P;reject(proof,bad)
    return {'degree_bound':degree,'domain_size':domain,'lanes':lanes,
            'root_hex':root.hex(),'coefficient_payload_bytes':degree*lanes*16,
            'mutations_rejected':rejected}


def main():
    binary,report=sys.argv[1:]
    cases=[run(binary,*shape) for shape in [(1,4,1),(4,16,3),(16,64,2)]]
    result={'status':'PASS','cases':cases,
            'scope':'New SHA384 Ext4 stage terminal, fully reconstructed oracle plus residual; not yet WHIR integrated',
            'validation':'Independent direct power-sum oracle, Rust SHA384 tree, separate convolution residual',
            'limits':['Diagnostic Ext4 only; no128-bitPQ claim','Preceding folding/proximity rounds remain unproved',
                      'Coefficient disclosure is not zero knowledge','Payload bytes exclude proof framing']}
    Path(report).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
