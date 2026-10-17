"""Deterministic quotient of columns equated by unconditional AIR constraints.
All constraints and interactions are retained and rewritten, including next-row
references. This is a separate canonical AIR, not a wire-compatible old profile.
"""
import copy

def mapping(table):
    width=table['width'];parent=list(range(width));edges=[]
    def find(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    for ci,e in enumerate(table['constraints']):
        if (len(e)==3 and e[0]=='+' and e[1][0]=='v' and e[2][0]=='-' and e[2][1][0]=='v'):
            a,b=e[1],e[2][1]
            if a[2]==b[2]==0:
                x,y=find(a[1]),find(b[1]);parent[max(x,y)]=min(x,y);edges.append((ci,a[1],b[1]))
    representatives=sorted({find(i) for i in range(width)});position={r:i for i,r in enumerate(representatives)}
    return dict(old_width=width,new_width=len(representatives),representatives=representatives,
                old_to_new=[position[find(i)] for i in range(width)],equality_constraints=edges)

def rewrite(e,plan):
    if e[0]=='v':return ['v',plan['old_to_new'][e[1]],e[2]]
    if e[0] in ('+','*'):return [e[0],rewrite(e[1],plan),rewrite(e[2],plan)]
    if e[0]=='-':return ['-',rewrite(e[1],plan)]
    return e.copy()

def quotient(air):
    result=copy.deepcopy(air);plans=[]
    for table in result['tables']:
        plan=mapping(table);plans.append(plan);table['width']=plan['new_width']
        table['constraints']=[rewrite(e,plan) for e in table['constraints']]
        for interaction in table['interactions']:
            interaction['mult']=[rewrite(e,plan) for e in interaction['mult']]
            interaction['msg']=[rewrite(e,plan) for e in interaction['msg']]
    return result,plans

def project(rows,plan):
    if any(len(r)!=plan['old_width'] for r in rows):raise ValueError('original witness width')
    reduced=[[r[i] for i in plan['representatives']] for r in rows]
    for original,new in zip(rows,reduced):
        if any(original[i]!=new[j] for i,j in enumerate(plan['old_to_new'])):
            raise ValueError('witness violates a quotient equality')
    return reduced

def lift(rows,plan):
    if any(len(r)!=plan['new_width'] for r in rows):raise ValueError('quotient witness width')
    return [[r[i] for i in plan['old_to_new']] for r in rows]
