"""Measure v2 dynamic SHA384 work after trusted fixed-layout key preparation."""
import gzip,hashlib,json,struct,types
import pq384_primitives as p
import pq384_terminal_gkr as g
import swirl_binary_transcript as binary
from swirl_fixed_gkr_verifier import prepare
from prove_swirl_binary_root import context,OUT as GKR,SOURCE
from prove_swirl_weighted_dag import split_obligation


def main():
    layout,slots,known,claim,statement,_=context()
    from swirl_bundle_codec import decode_gkr
    sections=binary.unpack_v2((GKR.parent/'binary-root-bundle/proof.bin').read_bytes())
    proof=decode_gkr(layout,sections[1])
    events=[];draws=[]
    def hp(tag,*parts):
        wire=p.PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts))+b''.join(p.u64(len(x))+x for x in parts)
        digest=hashlib.sha384(wire).digest();assert digest==p.hash_parts(tag,*parts)
        events.append(dict(tag=tag.decode(),bytes=len(wire),blocks=(len(wire)+144)//128,digest=digest.hex()))
        return digest
    def clone(f,**changes):return types.FunctionType(f.__code__,dict(f.__globals__,**changes),argdefs=f.__defaults__)
    st=clone(binary.statement,hash_parts=hp)((SOURCE/'prefix.bin').read_bytes());assert st==statement
    binding=clone(binary.binding,hash_parts=hp)(st,layout,proof)
    assert binding==(GKR/'gkr-binding.bin').read_bytes()
    boundary=events.copy();events.clear()
    methods={name:clone(getattr(p.Transcript,name),hash_parts=hp) for name in ('__init__','commit','draw')}
    base_draw=methods['draw']
    def draw(self,*args,**kwargs):
        result,meta=base_draw(self,*args,**kwargs);draws.append(meta);return result,meta
    methods['draw']=draw
    cls=type('CapturedBinaryTranscript',(),methods)
    verifier=prepare(layout,hash_function=hp,transcript_type=cls)
    residual=split_obligation(verifier(statement,proof,claim),slots,known)
    expected=json.loads(gzip.decompress((GKR/'pcs-obligation.json.gz').read_bytes()))
    assert json.loads(json.dumps(residual))==expected
    old=json.loads((GKR.parent/'gkr-transcript-census/report.json').read_text())
    total=sum(e['blocks'] for e in events+boundary)
    report=dict(status='BINARY_TRANSCRIPT_HASH_CENSUS_VERIFIED',boundary=boundary,
        dynamic_gkr_blocks=sum(e['blocks'] for e in events),total_dynamic_blocks=total,
        previous_total=old['total_dynamic_with_external'],saved_blocks=old['total_dynamic_with_external']-total,
        challenges=len(draws),squeeze_blocks=sum(x['blocks'] for x in draws),rejected_words=sum(x['rejected_words'] for x in draws),
        limitations=['Different versioned transcript and fresh proof; not lossless old-proof conversion.',
                     'Fixed layout hash precomputed; native prefix/WHIR hashing excluded.',
                     'No hash circuit proof, QROM security or PQ128/full NEAR claim.'])
    out=GKR.parent/'binary-root-bundle';out.mkdir(exist_ok=True)
    (out/'hash-census.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'hash-events.json.gz').write_bytes(gzip.compress(json.dumps(events).encode(),mtime=0))
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
