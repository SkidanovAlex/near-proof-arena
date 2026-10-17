"""Full framed SHA384 relation from canonical per-block compression proofs.

Padding/IV/state links/truncation are explicit verifier checks. This is NOT a
full recursive verifier and does not prove Merkle-path membership by itself.
The expected framed input and digest are supplied externally by the caller.
"""
import struct
import pq384_global_bus as bus
from pq384_primitives import require,PREFIX
from capture_pq384_merkle_hash import frame
IV=[0xcbbb9d5dc1059ed8,0x629a292a367cd507,0x9159015a3070dd17,0x152fecd8f70e5939,
    0x67332667ffc00b31,0x8eb44a8768581511,0xdb0c2e0d64f98fa7,0x47b5481dbefa4fa4]


def padded(message):
    require(type(message)is bytes and len(message)<1<<61,'bounded hash message')
    return message+b'\x80'+bytes((111-len(message))%128)+(8*len(message)).to_bytes(16,'big')


def public_words(pub):
    require(isinstance(pub,list) and len(pub)==128 and all(type(x)is int and 0<=x<65536 for x in pub),'canonical public limbs')
    return [sum(pub[4*i+j]<<(16*j) for j in range(4)) for i in range(32)]


def boundaries(items,canonical_air,tag,parts,expected):
    require(type(tag)is bytes and len(tag)<1<<32 and isinstance(parts,list) and all(type(x)is bytes for x in parts),'framed input')
    require(type(expected)is bytes and len(expected)==48,'expected SHA384 digest')
    message=frame(tag,parts,PREFIX);input_bytes=padded(message)
    require(isinstance(items,list) and len(items)==len(input_bytes)//128,'exact padded block count');initial=IV
    for i,item in enumerate(items):
        require(set(item)=={'statement','proof'},'block item fields');statement=item['statement'];spec=statement['spec']
        require(set(statement)=={'spec','roots'} and spec['air']==canonical_air,'canonical compression AIR')
        require(spec['log_rows']==[7] and spec['source_packings']==[128] and spec['aux_packings']==[0] and spec['terminal_degree']==1,'compression profile')
        words=public_words(spec['public']);require(words[:8]==initial,'SHA384 IV/state chain')
        require(b''.join(x.to_bytes(8,'big') for x in words[8:24])==input_bytes[128*i:128*(i+1)],'ordered padded message blocks')
        initial=words[24:]
    require(b''.join(x.to_bytes(8,'big') for x in initial[:6])==expected,'SHA384 digest truncation')
    return True


def verify(items,canonical_air,tag,parts,expected):
    boundaries(items,canonical_air,tag,parts,expected)
    for item in items:
        statement=item['statement'];require(bus.verify(item['proof'],statement['spec'],[bytes.fromhex(x) for x in statement['roots']]),'compression proof')
    return True

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    packet=json.loads(Path(sys.argv[1]).read_text());trusted=json.loads(Path(sys.argv[2]).read_text());air=json.loads(Path(sys.argv[3]).read_text())['air']
    verify(packet,air,bytes.fromhex(trusted['tag_hex']),[bytes.fromhex(x) for x in trusted['parts_hex']],bytes.fromhex(trusted['expected_digest_hex']))
    print('PASS: complete framed SHA384 relation from all compression proofs; not a full recursive verifier')
