"""Ext8 terminal compiler candidate; not the Ext4 native round-kernel ABI.

Builds 11-word instructions with expanded public-challenge message weights,
using the same formula generator as the canonical specification path,
then uses the shared public-constant folding and DAG balancing compiler.
"""
import check_bus_program_formulas as formulas
import pq384_ext8_reference as f
from pq384_terminal_compile import compile_terminal


def compile_weighted(table, public, alpha, gamma, finals, mixing, protocol, *, expanded_messages=True):
    instructions=[];cache={}
    def emit(row):
        row=tuple(row)
        if row not in cache:
            cache[row]=len(instructions);instructions.append(row)
        return cache[row]
    def ast(e):
        op=e[0]
        if op=='lit':return emit((0,0,0,*f.canonical(e[1])))
        if op in ('current','next'):
            return emit((1 if op=='current' else 2,e[1],0,*f.ZERO))
        if op in ('first','last','trans'):
            return emit(({'first':3,'last':4,'trans':5}[op],0,0,*f.ZERO))
        return emit(({'add':6,'sub':7,'mul':8}[op],ast(e[1]),ast(e[2]),*f.ZERO))
    auxiliary,_=formulas.expected(table,public,f.canonical(alpha),f.canonical(gamma),finals,field=f,expanded_messages=expanded_messages)
    residuals=[formulas.expr(e,public,field=f) for e in protocol.constraints(table)]
    residuals += [e['formula'] for e in auxiliary]
    zero=ast(formulas.lit(f.ZERO));total=zero;weight=f.ONE
    for residual in residuals:
        value=ast(residual);w=ast(formulas.lit(weight))
        product=emit((8,w,value,*f.ZERO));total=emit((6,total,product,*f.ZERO))
        weight=f.mul(weight,f.canonical(mixing))
    # Preserve the last-register output convention even if CSE reuses it.
    instructions.append((6,total,zero,*f.ZERO))
    return [x for row in instructions for x in row]


def compile_ext8_terminal(spec,alpha,gamma,finals,terminals,rho):
    return compile_terminal(spec,alpha,gamma,finals,terminals,rho,
                            field=f,program_compiler=compile_weighted)
