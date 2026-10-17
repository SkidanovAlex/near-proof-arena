"""Bounded linear reassociation over Fp; preserves all original node outputs.

This is an executable arithmetic rewrite, not a Lean compiler proof.
"""
import heapq

P=2013265921


def rebalance(nodes, requested):
    result=[]; depths=[]; intern={}; forms=[]; mapped=[]; atoms={}
    def emit(node):
        node=tuple(node)
        if node in intern:return intern[node]
        idx=len(result);intern[node]=idx;result.append(node)
        depths.append(0 if node[0] in ('const','input') else 1+max(depths[node[1]],depths[node[2]]))
        return idx
    def const(c):return emit(('const',c%P,0,0,0))
    def build(form):
        terms=[]
        for atom,coefficient in sorted(form.items()):
            if atom==-1:idx=const(coefficient)
            else:
                idx=atoms[atom]
                if coefficient!=1:idx=emit(('mul',idx,const(coefficient)))
            heapq.heappush(terms,(depths[idx],idx))
        if not terms:return const(0)
        while len(terms)>1:
            _,a=heapq.heappop(terms);_,b=heapq.heappop(terms)
            idx=emit(('add',a,b));heapq.heappush(terms,(depths[idx],idx))
        return terms[0][1]
    for i,(op,*args) in enumerate(nodes):
        if op=='const':form={-1:args[0]} if args[0] else {}
        elif op=='input':atoms[i]=emit((op,*args));form={i:1}
        else:
            a,b=args;assert 0<=a<i and 0<=b<i
            if op in ('add','sub'):
                form=forms[a].copy();sign=1 if op=='add' else -1
                for k,v in forms[b].items():form[k]=(form.get(k,0)+sign*v)%P
                form={k:v for k,v in form.items() if v}
            elif op=='mul' and (set(forms[a]) <= {-1} or set(forms[b]) <= {-1}):
                c,other=(forms[a].get(-1,0),forms[b]) if set(forms[a]) <= {-1} else (forms[b].get(-1,0),forms[a])
                form={k:c*v%P for k,v in other.items() if c*v%P}
            else:
                assert op=='mul';atoms[i]=emit((op,mapped[a],mapped[b]));form={i:1}
            if len(form)>512:
                atoms[i]=emit((op,mapped[a],mapped[b]));form={i:1}
        forms.append(form);mapped.append(build(form))
    return result,[mapped[i] for i in requested]
