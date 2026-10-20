"""Mandatory-root/profile/complete-opening rejection checks for direct input."""
import argparse,copy,json,sys
from pathlib import Path
from verify_sha384_direct import verify,check_public

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--proof-directory',required=True);p.add_argument('--baseline-proof-directory',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    out=Path(a.proof_directory);baseline=Path(a.baseline_proof_directory);st=json.loads((out/'statement.json').read_text());expected=json.loads((out/'expected-input.json').read_text());wire=(out/'proof.bin').read_bytes();old=json.loads((baseline/'expected-input.json').read_text())
    assert expected['input_root']==old['input_root'] and expected['input_context_hex']==old['input_context_hex'];assert expected['air_sha384']!=old['air_sha384'];assert verify(wire,st,expected)
    checks=[]
    def reject(name,w,s,e):
        try:verify(w,s,e)
        except (AssertionError,ValueError,IndexError,KeyError):checks.append(name)
        else:raise AssertionError(name)
    for name,alter in [('missing-root',lambda x:x.pop('input_root')),('wrong-root',lambda x:x.update(input_root='00'*48)),('wrong-length',lambda x:x.update(declared_length=375)),('wrong-context',lambda x:x.update(input_context_hex='00')),('wrong-air',lambda x:x.update(air_sha384='00'*48))]:
        bad=copy.deepcopy(expected);alter(bad);reject(name,wire,st,bad)
    reject('old-profile-receipt',wire,st,old)
    for name,w in [('truncated-wire',wire[:-1]),('trailing-wire',wire+b'\0'),('source-root-wire',wire[:6]+bytes([wire[6]^1])+wire[7:]),('opening-wire',wire[:-1]+bytes([wire[-1]^1]))]:reject(name,w,st,expected)
    bad=copy.deepcopy(st);bad['spec']['public'][0]^=1;reject('wrong-public-digest',wire,bad,expected)
    bad=copy.deepcopy(st);bad['spec']['air']['tables'][2]['interactions'][0]['msg'][0]={'const':1};reject('changed-tag-AIR',wire,bad,expected)
    # Check the layout predicate directly as well as the complete wrapper:
    # transcript mismatch alone must not account for these rejections.
    assert check_public(st['spec']['public'])
    layout_checks=[]
    mutations=[('digest-negative',0,-1),('digest-overflow',0,256),
               ('digest-bool',0,True),('digest-float',0,1.0),('digest-string',0,'1')]
    mutations += [(f'fixed-public-{i}',i,st['spec']['public'][i]^1) for i in range(48,88)]
    for name,index,value in mutations:
        bad=copy.deepcopy(st);bad['spec']['public'][index]=value
        try:check_public(bad['spec']['public'])
        except (AssertionError,ValueError):layout_checks.append(name)
        else:raise AssertionError(name)
        reject(name,wire,bad,expected)
    for name,public in [('public-short',st['spec']['public'][:-1]),('public-long',st['spec']['public']+[0])]:
        try:check_public(public)
        except (AssertionError,ValueError):layout_checks.append(name)
        else:raise AssertionError(name)
        bad=copy.deepcopy(st);bad['spec']['public']=public;reject(name,wire,bad,expected)
    report=dict(status='PASS',negative_tests=checks,canonical_layout_rejections=layout_checks,mandatory_original_input_root_and_context_preserved=True,changed_AIR_digest_required=True,scope='Complete binary verification mandatory; no security or zero-knowledge claim.')
    (out/'direct-negatives.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
