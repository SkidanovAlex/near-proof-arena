"""Closed linear routing for a bounded private Merkle-path SHA384 call table.

Public statement alone determines all equations. Siblings are witness message
limbs; no expected call list or native Merkle result is a verifier input.
These equations MUST be composed with the actual compression/use AIR and a
same-root proof of every equation. This module alone is not a proof system.
"""
import struct
from pq384_primitives import PREFIX, P, require, u64
from certify_sha384_occurrence_chains import IV

PROFILE='near-private-merkle-call-routing-v1'


def checked_statement(statement):
    require(type(statement)is dict and set(statement)=={'profile','context_hex','root_hex','leaf_hex','leaf_count','index'},'public statement fields')
    require(statement['profile']==PROFILE,'routing profile')
    def binary(key):
        value=statement[key]
        require(type(value)is str,'hex string')
        result=bytes.fromhex(value)
        require(result.hex()==value,'canonical lowercase hex')
        return result
    context,root,leaf=[binary(k) for k in ('context_hex','root_hex','leaf_hex')]
    count,index=statement['leaf_count'],statement['index']
    require(type(count)is int and 2<=count<=16 and count&(count-1)==0,'bounded complete path depth')
    require(type(index)is int and 0<=index<count,'public leaf position')
    require(len(root)==48,'root width')
    require(1<=len(context)<=255 and len(context)%2==1,'odd context gives aligned private digest limbs')
    require(len(leaf)<=64 and len(leaf)%2==0,'bounded even public leaf bytes')
    return context,root,leaf,count,index


def framed(tag,parts):
    result=list(PREFIX+struct.pack('<I',len(tag))+tag+struct.pack('<I',len(parts)))
    for part in parts: result+=list(u64(len(part)))+list(part)
    return result


def message_column(offset):
    require(type(offset)is int and 0<=offset<128 and offset%2==0,'16-bit byte pair')
    return 35+4*(offset//8)+3-(offset%8)//2


def compile_routes(statement):
    context,root,leaf,count,index=checked_statement(statement)
    calls=[];equations=[];private_pairs=[];cursor=0
    def equation(terms,value=0):
        # (row,column,integer coefficient) entries; column-major flattening later.
        equations.append({'terms':[list(t) for t in terms],'constant':value})
    def emit(tag,parts):
        nonlocal cursor
        message=framed(tag,parts);length=len(message)
        padded=message+[128]+[0]*((111-length)%128)+list((8*length).to_bytes(16,'big'))
        rows=list(range(cursor,cursor+len(padded)//128));cursor+=len(rows)
        for step,row in enumerate(rows):
            for j in range(32):
                if step==0:
                    word=int.from_bytes(IV[8*(j//4):8*(j//4+1)],'big')
                    equation([(row,3+j,1)],(word>>(16*(j%4)))&65535)
                else: equation([(row,3+j,1),(rows[step-1],99+j,-1)])
            for off in range(0,128,2):
                pair=padded[128*step+off:128*step+off+2];col=message_column(off)
                if all(type(x)is tuple and x[0]=='private' for x in pair):
                    require(pair[0][1]==pair[1][1] and pair[1][2]==pair[0][2]+1,'contiguous sibling bytes')
                    private_pairs.append({'row':row,'column':col,'level':pair[0][1],'byte':pair[0][2]})
                    continue
                terms=[(row,col,1)];constant=0
                for x,weight in zip(pair,(256,1)):
                    if type(x)is int:
                        require(0<=x<256,'constant byte');constant+=weight*x
                    else:
                        require(type(x)is tuple and len(x)==3 and x[0]=='digest' and x[1]<rows[0] and 0<=x[2]<48,'prior digest byte routing')
                        terms.append((x[1],131+x[2],-weight))
                equation(terms,constant)
        calls.append({'tag':tag.decode(),'message':message,'rows':rows})
        return [('digest',rows[-1],j) for j in range(48)]
    value=emit(b'merkle/leaf',[context,u64(index),leaf])
    position=index
    for level in range(1,count.bit_length()):
        sibling=[('private',level,j) for j in range(48)]
        left,right=(sibling,value) if position&1 else (value,sibling)
        value=emit(b'merkle/node',[context,u64(level),left,right]);position//=2
    value=emit(b'merkle/root',[context,u64(count),value])
    for j,byte in enumerate(root):equation([(value[j][1],131+j,1)],byte)
    require(cursor<=25,'current compression chunk capacity')
    require(len(private_pairs)==24*(count.bit_length()-1),'every private sibling byte accounted for')
    require(len({(p['row'],p['column']) for p in private_pairs})==len(private_pairs),'private cells distinct')
    return dict(profile=PROFILE,statement=statement,use_count=cursor,row_count=1<<cursor.bit_length(),
        equations=equations,private_pairs=private_pairs,calls=calls,
        required_consumer='Compression/use AIR on these exact rows and a same-commitment proof of all routing equations; caller must not replace that AIR proof with this evaluator.')


def residuals(program,rows):
    require(len(rows)==program['row_count'] and all(len(row)==179 for row in rows),'exact use-table shape')
    require(all(type(x)is int and 0<=x<P for row in rows for x in row),'canonical field cells')
    return [(sum(rows[r][c]*w for r,c,w in e['terms'])-e['constant'])%P for e in program['equations']]


def flatten_equations(program):
    n=program['row_count']
    return [{'terms':[[r+n*c,w] for r,c,w in e['terms']],'constant':e['constant']} for e in program['equations']]


def witness_rows(statement,path,probe):
    """Honest generator only; path and Probe never enter compile_routes."""
    program=compile_routes(statement)
    require(type(path)is list and len(path)==statement['leaf_count'].bit_length()-1 and
            all(type(x)is bytes and len(x)==48 for x in path),'private path shape')
    rows=[[0]*179 for _ in range(program['row_count'])]
    def limbs(raw):
        return [(int.from_bytes(raw[i:i+8],'big')>>(16*j))&65535 for i in range(0,len(raw),8) for j in range(4)]
    for call in program['calls']:
        def byte(x):
            if type(x)is int:return x
            if x[0]=='private':return path[x[1]-1][x[2]]
            return rows[x[1]][131+x[2]]
        message=bytes(byte(x) for x in call['message']);padded,states=probe.run(message)
        require(len(padded)==128*len(call['rows']),'fixed canonical block count')
        for step,row in enumerate(call['rows']):
            initial=struct.pack('>8Q',*states[step]);final=struct.pack('>8Q',*states[step+1])
            rows[row]=[row,1,row]+limbs(initial)+limbs(padded[128*step:128*(step+1)])+limbs(final)+list(final[:48])
    return program,rows


def check_routing(statement,rows):
    """Only public-statement entry: never accept a prover-selected program."""
    return not any(residuals(compile_routes(statement),rows))
