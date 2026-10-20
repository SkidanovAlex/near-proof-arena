"""Experimental closed adapter with versioned, derived-functional stage binding.
Only full adapter prove/verify are public entry points. No QROM certification.
The standalone stage implementation is untouched and still binds explicit weights.
"""
import types
import ext8_code_switch_stage as original_stage
import ext8_weighted_code_switch as original_adapter

PROFILE='near-ext8-closed-derived-switch-experiment-v1'
STAGE_PROFILE='near-ext8-closed-derived-stage-experiment-v1'
DERIVATION=b'input-equality/adjacent-affine-fold/monomial-injection/v1'


def _clone(module,name):
    """Isolate function globals, including mutually calling helpers; no patching."""
    result=types.ModuleType(name);result.__dict__.update(vars(module));result.__name__=name
    for key,value in vars(module).items():
        if isinstance(value,types.FunctionType) and value.__module__==module.__name__:
            fn=types.FunctionType(value.__code__,result.__dict__,value.__name__,value.__defaults__,value.__closure__)
            fn.__kwdefaults__=value.__kwdefaults__;result.__dict__[key]=fn
    return result


_stage=_clone(original_stage,__name__+'._stage')
_stage.PROFILE=STAGE_PROFILE


def _derived_start(config,weights,claim):
    # Same geometry/canonical checks as original start. The full adapter derives
    # weights from input-reduction challenges and authenticated prior stages.
    h=_stage.h;f=_stage.f
    h.require(type(config)is dict and set(config)=={'profile','degree','blowup','fold_bits','next_blowup','next_fold_bits','queries','namespace','parent','root'},'stage config fields')
    h.require(config['profile']==STAGE_PROFILE,'closed stage profile')
    N,count,omega=_stage.geometry(config['degree'],config['blowup'],config['fold_bits'])
    h.require(config['fold_bits']>0,'positive stage folding')
    _stage.geometry(config['degree']>>config['fold_bits'],config['next_blowup'],config['next_fold_bits'])
    h.require(type(config['queries'])is int and 1<=config['queries']<=4095,'query count')
    for key in ('namespace','parent','root'):_stage.hashread(config[key])
    h.require(len(weights)==config['degree'],'weight shape');weights=[f.canonical(w) for w in weights];claim=f.canonical(claim)
    seed=h.hash_parts(STAGE_PROFILE.encode(),DERIVATION,_stage.canonical_json(config),_stage.extbytes(claim))
    return h.Transcript(seed),weights,claim,N,count,omega


_stage.start=_derived_start
_adapter=_clone(original_adapter,__name__+'._adapter')
_adapter.stage=_stage
_adapter.PROFILE=PROFILE


def prove(caches,native,statement,parent,branches,claim,config):
    return _adapter.prove(caches,native,statement,parent,branches,claim,config)


def verify(proof,statement,parent,branches,claim,config,*,native=None):
    return _adapter.verify(proof,statement,parent,branches,claim,config,native=native)


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    p=argparse.ArgumentParser();p.add_argument('--proof',type=Path,required=True);p.add_argument('--statement',type=Path,required=True);a=p.parse_args()
    s=json.loads(a.statement.read_text());verify(json.loads(a.proof.read_text()),bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),s['branches'],s['claim'],s['config'])
    print('PASS closed derived-functional experiment; no security certificate.')
