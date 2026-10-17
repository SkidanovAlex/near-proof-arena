"""Experimental affine-region DAG rewrite; existing verifier/compiler unchanged.
Shared intermediate expressions remain region boundaries. No formal compiler
refinement claim: differential evaluation and layer certificates are separate.
"""
import heapq
import pq384_ext8_reference as f


def rebalance(circuit):
    old=circuit['nodes'];live=set(circuit['live_nodes']);uses=[0]*len(old)
    for i in live:
        if old[i][0] in ('add','sub','mul'):
            for child in old[i][1:]:uses[child]+=1
    nodes=[];cache={};depth=[];mapped={};regions=[]
    def emit(node):
        node=tuple(node)
        if node not in cache:
            cache[node]=len(nodes);nodes.append(node)
            depth.append(0 if node[0] in ('const','input') else 1+max(depth[node[1]],depth[node[2]]))
        return cache[node]
    def const(value):return emit(('const',*value))
    zero=const(f.ZERO)
    def operation(op,a,b):
        if nodes[a][0]==nodes[b][0]=='const':return const({'add':f.add,'sub':f.sub,'mul':f.mul}[op](nodes[a][1:],nodes[b][1:]))
        if op=='add':
            if a==zero:return b
            if b==zero:return a
        if op=='mul':
            if a==zero or b==zero:return zero
            if nodes[a]==('const',*f.ONE):return b
            if nodes[b]==('const',*f.ONE):return a
        return emit((op,a,b))
    def build(i):
        if i in mapped:return mapped[i]
        node=old[i]
        if node[0] in ('const','input'):result=emit(node)
        elif node[0]=='mul' and all(old[j][0]!='const' for j in node[1:]):result=operation('mul',build(node[1]),build(node[2]))
        else:
            terms={};constant=f.ZERO;visited=0
            def collect(j,scale,root=False):
                nonlocal constant,visited
                visited+=1;n=old[j];op=n[0]
                if op=='const':constant=f.add(constant,f.mul(scale,n[1:]));return
                if not root and uses[j]>1:
                    terms[j]=f.add(terms.get(j,f.ZERO),scale);return
                if op in ('add','sub'):
                    collect(n[1],scale);collect(n[2],scale if op=='add' else f.sub(f.ZERO,scale));return
                if op=='mul':
                    for pos in (1,2):
                        if old[n[pos]][0]=='const':
                            collect(n[3-pos],f.mul(scale,old[n[pos]][1:]));return
                terms[j]=f.add(terms.get(j,f.ZERO),scale)
            collect(i,f.ONE,True)
            heap=[];serial=0
            for j,weight in terms.items():
                if weight==f.ZERO:continue
                value=operation('mul',const(weight),build(j))
                heapq.heappush(heap,(depth[value],serial,value));serial+=1
            if constant!=f.ZERO:heapq.heappush(heap,(0,serial,const(constant)));serial+=1
            while len(heap)>1:
                _,_,a=heapq.heappop(heap);_,_,b=heapq.heappop(heap)
                value=operation('add',a,b);heapq.heappush(heap,(depth[value],serial,value));serial+=1
            result=heap[0][2] if heap else zero
            regions.append(dict(source=i,target=result,visited=visited,atoms=len(terms)))
        mapped[i]=result;return result
    root=build(circuit['root'])
    if nodes[root][0] in ('const','input'):root=emit(('add',root,zero))
    reachable=set();todo=[root]
    while todo:
        i=todo.pop()
        if i in reachable:continue
        reachable.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    result={**circuit,'nodes':nodes,'root':root,'live_nodes':sorted(reachable)}
    return result,dict(regions=len(regions),largest_region=max((x['visited'] for x in regions),default=0),root_depth=depth[root])
