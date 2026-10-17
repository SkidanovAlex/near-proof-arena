#!/usr/bin/env python3
"""Full-data RS/Merkle diagnostic, NOT a succinct or WHIR verifier."""
import argparse
from copy import deepcopy
import hashlib,json,struct
from pathlib import Path
P=2013265921

def words(xs):
    if any(type(x)is not int or not 0<=x<2**32 for x in xs):raise ValueError('u32')
    return struct.pack('<'+'I'*len(xs),*xs)

def opening(q,root):
    try:
        raw=q['raw_words'];index=q['tree_index']
        if len(raw)!=2 or any(len(r)!=104 for r in raw):return False
        if any(type(x)is not int or not 0<=x<P for r in raw for x in r):return False
        if type(index)is not int or not 0<=index<16 or len(q['path'])!=4:return False
        h=hashlib.blake2s(words([raw[o][c] for c in range(104) for o in range(2)])).digest()
        for sibling in q['path']:
            if len(sibling)!=8:return False
            b=words(sibling);h=hashlib.blake2s(b+h if index&1 else h+b).digest();index>>=1
        return h==words(root)
    except (ValueError,KeyError,TypeError):return False

def verify(data,source):
    assert data['field_modulus']==source['field_modulus']==P
    assert data['columns']==source['columns']==104
    assert data['hash']=='BLAKE2s-256, 10 rounds'
    assert data['lde_factor']==4 and data['values_per_leaf']==2
    rows=source['rows'];assert rows==data['rows'] and len(rows)==8
    assert all(len(r)==104 and all(type(v)is int and 0<=v<P for v in r) for r in rows)
    generator=data['domain_root'];assert pow(generator,8,P)==1 and pow(generator,4,P)!=1
    cw=data['codewords'];assert len(cw)==4
    assert len({pow(x['offset'],8,P) for x in cw})==4
    for co in cw:assert len(co['columns'])==104 and all(len(c)==8 for c in co['columns'])
    checks=0
    for c in range(104):
        coeff=[r[c] for r in rows]
        for bit in (1,2,4):
            for i in range(8):
                if i&bit:coeff[i]=(coeff[i]-coeff[i^bit])%P
        for co in cw:
            for j in range(8):
                x=co['offset']*pow(generator,j,P)%P
                expected=sum(a*pow(x,i,P) for i,a in enumerate(coeff))%P
                assert co['columns'][c][j]==expected,'RS mismatch'
                checks+=1
    qs=data['openings'];assert len(qs)==16 and sorted(q['query'] for q in qs)==list(range(16))
    for q in qs:
        i=q['query'];co=i%4;internal=i//4;reverse=((co&1)<<1)|(co>>1)
        assert q['coset']==co and q['tree_index']==reverse*4+internal
        expected=[[cw[co]['columns'][c][internal+o*4] for c in range(104)] for o in range(2)]
        assert q['values']==expected
        assert q['raw_words']==[[v*2**32%P for v in r] for r in expected]
        assert opening(q,data['root']),'Merkle mismatch'
    rejected=0
    for q in qs:
        for kind in ('leaf','sibling','index','noncanonical'):
            bad=deepcopy(q)
            if kind=='leaf':bad['raw_words'][0][0]=(bad['raw_words'][0][0]+1)%P
            elif kind=='sibling':bad['path'][0][0]^=1
            elif kind=='index':bad['tree_index']^=1
            else:bad['raw_words'][0][0]=P
            assert not opening(bad,data['root']),kind
            rejected+=1
    return {'status':'PASS','rs_evaluations_checked':checks,'merkle_openings_checked':16,
      'opening_mutations_rejected':rejected,'hash':'full-round BLAKE2s-256',
      'witness_rows':8,'witness_columns':104,'root_hex':words(data['root']).hex(),
      'scope':'Independent full-data RS encoding and Merkle inclusion diagnostics.',
      'whir_proximity_proof_generated':False,'gkr_proof_generated':False,'quantum_security_established':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('data','source','report'):p.add_argument(name,type=Path)
    a=p.parse_args();result=verify(json.loads(a.data.read_text()),json.loads(a.source.read_text()))
    result['sha256']={str(x):hashlib.sha256(x.read_bytes()).hexdigest() for x in [a.data,a.source,Path(__file__)]}
    a.report.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
