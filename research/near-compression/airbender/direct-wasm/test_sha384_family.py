"""Bounded framing/public contract, mandatory root and complete-wire negatives."""
import argparse,copy,json,sys
from pathlib import Path
from verify_sha384_family import verify,fixed_contract,canonical_public

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--proof-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    out=Path(a.proof_directory);st=json.loads((out/'statement.json').read_text());receipt=json.loads((out/'expected-input.json').read_text());wire=(out/'proof.bin').read_bytes();assert verify(wire,st,receipt);tests=[]
    def reject(name,w,s,e):
        try:verify(w,s,e)
        except (AssertionError,ValueError,IndexError,KeyError,TypeError):tests.append(name)
        else:raise AssertionError(name)
    for name,change in [('missing-root',lambda e:e.pop('input_root')),('wrong-root',lambda e:e.update(input_root='00'*48)),('wrong-context',lambda e:e.update(input_context_hex='00')),('wrong-AIR',lambda e:e.update(air_sha384='00'*48)),('wrong-length',lambda e:e.update(declared_length=e['declared_length']+1)),('bool-length',lambda e:e.update(declared_length=True)),('length-zero',lambda e:e.update(declared_length=0)),('length-over-bound',lambda e:e.update(declared_length=1025)),('missing-framing',lambda e:e.pop('fixed_framing')),('changed-framing-byte',lambda e:e['fixed_framing'][0].__setitem__(1,e['fixed_framing'][0][1]^1)),('duplicate-framing-index',lambda e:e['fixed_framing'].insert(1,e['fixed_framing'][0][:])),('out-of-range-framing-index',lambda e:e['fixed_framing'][-1].__setitem__(0,e['declared_length'])),('bool-framing-byte',lambda e:e['fixed_framing'][0].__setitem__(1,True))]:
        bad=copy.deepcopy(receipt);change(bad);reject(name,wire,st,bad)
    for name,index,value in [('wrong-IV',52,st['spec']['public'][52]^1),('wrong-digest-count',48,0),('wrong-IV-count',84,0),('digest-byte256',0,256),('digest-negative',0,-1),('digest-bool',0,True),('count-bool',48,True),('IV-bool',52,True),('digest-field-alias',0,2013265921+st['spec']['public'][0]),('IV-field-alias',52,2013265921+st['spec']['public'][52])]:
        bad=copy.deepcopy(st);bad['spec']['public'][index]=value;reject(name,wire,bad,receipt)
    bad=copy.deepcopy(st);bad['spec']['public'][0]^=1;reject('different-byte-digest',wire,bad,receipt)
    for name,w in [('truncated-wire',wire[:-1]),('trailing-wire',wire+b'\0'),('source-root-wire',wire[:6]+bytes([wire[6]^1])+wire[7:]),('opening-wire',wire[:-1]+bytes([wire[-1]^1]))]:reject(name,w,st,receipt)
    fixed_contract(1,[[0,0]]);fixed_contract(1024,[[0,255],[1023,0]]);canonical_public(st['spec']['public'])
    report=dict(status='PASS',negative_tests=tests,contract_boundary_checks=[1,1024],strict_canonical_public=True,mandatory_external_root=True,scope='Only selected actual267B representative has complete proof evidence; endpoint length checks are contract validation, not extra proved traces. No zero-knowledge/security certification.')
    (out/'family-negatives.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
