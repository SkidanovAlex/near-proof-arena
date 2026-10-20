"""Instantiate the checked-fold bound from retained diagnostic geometry."""
import argparse,gzip,hashlib,json,math
from fractions import Fraction
from pathlib import Path


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2]
    proofpath=package/'results/ext8-call-pcs/proof.json.gz'
    proof=json.loads(gzip.decompress(proofpath.read_bytes()))['opening']
    # The actual weighted joint verifier uses rate4 and halves once per round.
    rounds=len(proof['rounds']);degree=1<<rounds;domain=4*degree;queries=len(proof['queries'])
    source=package/'results/ext8-linked-calls/statement.json.gz'
    st=json.loads(gzip.decompress(source.read_bytes()));actual_degree=(1<<st['spec']['log_rows'][3])*st['spec']['source_packings'][3]
    assert actual_degree==degree and len(proof['reduction'])==rounds
    threshold=(2*domain+degree)//3+1
    assert 2*domain+degree<3*threshold<=3*domain
    assert threshold==1 or not 2*domain+degree<3*(threshold-1)
    agreement=Fraction(threshold-1,domain);query_term=agreement**queries
    field=2013265921**4
    fold_numerator=sum(max(domain>>(i+1),2) for i in range(rounds))
    conditional=Fraction(fold_numerator,field)+query_term
    def needed(bits):
        q=0
        while agreement**q>Fraction(1,1<<bits):q+=1
        assert q==0 or agreement**(q-1)>Fraction(1,1<<bits)
        return q
    targets={str(bits):needed(bits) for bits in (128,198,220)}
    report=dict(status='DIAGNOSTIC_QUERY_TERM_DOES_NOT_CERTIFY_TARGET',source_degree=degree,source_domain=domain,
        folds=rounds,queries=queries,min_threshold=threshold,max_surviving_queries=threshold-1,
        agreement_fraction=str(agreement),query_term_exact=str(query_term),query_term=float(query_term),
        query_term_negative_log2=-math.log2(float(query_term)),fold_numerator=fold_numerator,
        ideal_near_conditional_bound=float(conditional),
        minimal_queries_for_isolated_query_term=targets,
        far_outer_degree_numerator=rounds*max(domain,2),
        assumptions=['Ideal independent uniform fold challenges and source query indices',
          'Verified local fold/terminal checks and fixed prior snapshots, weights and claims',
          'Near branch: fixed jointly-close source tuple, separation and wrong functional',
          'Far branch: separate multiaffine source-batching hypotheses'],
        excluded=['Functional reduction error','Hash/commitment extraction error','Fiat-Shamir/QROM reduction','Full recursive verifier and NEAR execution'],
        scope='Exact instantiation of existing conditional ideal bounds, not an attack success lower bound. Raising query count alone cannot establish a target: the Ext4 field term is already too large for128bits. 198/220 are component-budget examples, not asserted quantum-security conversions. No complete proof-size projection or security certificate.',
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in
          [Path(__file__),proofpath,source,package/'NearCompression/CheckedHistoryNear.lean',package/'NearCompression/CheckedHistorySource.lean']})
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
