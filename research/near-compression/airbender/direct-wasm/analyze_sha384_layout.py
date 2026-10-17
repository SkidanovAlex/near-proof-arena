"""Exact source dependencies and explicitly conditional next-layout estimates."""
import argparse,collections,hashlib,json
from pathlib import Path
import pq384_column_quotient as quotient

def degree(e):
    if e[0]=='v':return 1
    if e[0]=='-':return degree(e[1])
    if e[0]=='+':return max(degree(e[1]),degree(e[2]))
    if e[0]=='*':return degree(e[1])+degree(e[2])
    return 0

def columns(e):
    if e[0]=='v':return {e[1]}
    if e[0]=='-':return columns(e[1])
    if e[0] in ('+','*'):return columns(e[1])|columns(e[2])
    return set()

def main():
    p=argparse.ArgumentParser();p.add_argument('--spec',required=True);p.add_argument('--hash-accounting',required=True);p.add_argument('--output',required=True);a=p.parse_args()
    raw=Path(a.spec).read_bytes();spec=json.loads(raw);new,plans=quotient.quotient(spec['air']);table=new['tables'][0];plan=plans[0];account=json.loads(Path(a.hash_accounting).read_text());blocks=account['identical_hash_inputs_shared']['compression_blocks']
    groups=collections.Counter('schedule' if c<2544 else 'round' if c<5152 else 'phase' if c<5280 else 'feedforward' for c in range(plan['old_width']) if c not in plan['representatives'])
    candidates={}
    for ci,e in enumerate(table['constraints']):
        if e[0]=='+' and e[1][0]=='v' and e[2][0]=='-' and e[1][2]==0:
            c=e[1][1];rhs=e[2][1]
            if c not in columns(rhs) and degree(rhs)<=1:candidates[c]=(ci,rhs)
    visiting=set();done=set()
    def visit(c):
        if c in visiting:raise ValueError('cyclic linear substitution')
        if c in done:return
        visiting.add(c)
        for d in columns(candidates[c][1]) & candidates.keys():visit(d)
        visiting.remove(c);done.add(c)
    for c in candidates:visit(c)
    def cost(cells):return dict(cells_per_compression=cells,raw_u32_bytes=blocks*cells*4,raw_u32_gib=blocks*cells*4/2**30)
    report=dict(original_spec_sha256=hashlib.sha256(raw).hexdigest(),deduplicated_compression_blocks=blocks,
        original=cost(128*6944),implemented_column_quotient=cost(128*6336),removed_columns_by_original_region=dict(groups),
        alias_constraint_indices=[x[0] for x in plan['equality_constraints']],next_linear_substitution_candidate_columns=len(candidates),linear_dependency_graph_acyclic=True,
        ranked_next_steps=[
          dict(rank=1,change='Acyclic linear limb/constant substitution after alias quotient',estimated=cost(128*(6336-len(candidates))),
               status='184 actual degree-at-most-one definitions, acyclic; not implemented',obligations='Expr substitution and trace expansion with affine current/next reconstruction; preserve all rewritten constraints; measure AST expansion cost'),
          dict(rank=2,change='Separate feed-forward endpoint table',estimated=cost(128*5280+1664),
               status='Ideal fully occupied batched endpoint rows; excludes new routing/auxiliaries/power-of-two slack',
               obligations='Feed-forward currently constrained on every row and first-state bits propagated across128rows; route initial/end state once to endpoint add table, prove unique block tags and addition semantics'),
          dict(rank=3,change='Batch80round blocks in one trace instead of128rows per block',estimated=cost(80*5280+1664),
               status='Ideal combined with endpoint split; excludes reset/phase/routing columns and global power-of-two slack',
               obligations='Current phaseLast atrow127 and every-row sequences forbid simple truncation; replace phase/height contract, gate state/window resets at block starts, prove all80round ordering and endpoints'),
          dict(rank=4,change='Replace128one-hot phase columns with binary index/fixed-key lookup',columns_saved_upper_bound=121,
               status='Not implemented;121 assumes7counterbits and excludes carries/lookupaux',obligations='Bind actual round index and key limbs, endpoint79, initial/final selectors and exact trace shape')],
        limits=['Dense source cells only, not prover peak memory/FFT/auxiliary cost','Actual accepted profile remains Q8 diagnostic; no recursive verifier or128bit claim','Candidate estimates are not proven implementation savings'])
    Path(a.output).write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='alias_constraint_indices'},indent=2))
if __name__=='__main__':main()
