"""Executable parity for the tagged fingerprint adapter, not soundness certification."""
import hashlib
import json
from pathlib import Path
from reference import public_messages
import verify_whir_toy as ext4
import pq384_ext8_reference as ext8


def horner(e, alpha, message):
    result = e.ZERO
    for value in reversed(message):
        result = e.add(e.base(value), e.mul(alpha,result))
    return result


def verifier_encoding(e, alpha, bus, message):
    # The increasing-power loop used by global_fingerprint_balance.
    fp, power = e.ZERO,e.ONE
    for value in message:
        fp = e.add(fp,e.mul(e.base(value),power))
        power = e.mul(power,alpha)
    return e.add(fp,e.mul(e.base(bus+1),power))


def main():
    package = Path(__file__).resolve().parents[2]
    directory = package/'results/pq384-code-table-long193'
    raw = (directory/'statement.json').read_bytes()
    spec = json.loads(raw)['spec']
    records = list(public_messages(spec['air'],spec['public']))
    assert {len(m) for _,_,m in records} == {25,27}
    width = 28
    tests = 0
    for e,degree in [(ext4,4),(ext8,8)]:
        challenges = [e.ZERO,e.ONE,tuple(range(1,degree+1)),tuple(e.P-i-1 for i in range(degree))]
        for alpha in challenges:
            for bus,_,message in records:
                assert 0 < bus+1 < e.P
                tagged = list(message)+[bus+1]
                padded = tagged+[0]*(width-len(tagged))
                assert verifier_encoding(e,alpha,bus,message) == horner(e,alpha,tagged) == horner(e,alpha,padded)
                restored = list(padded)
                while restored and restored[-1] == 0:
                    restored.pop()
                assert restored == tagged
                tests += 1
    # A zero tag would make unequal encodings identical after padding.
    assert [1]+[0]*2 == [1,0]+[0]
    report = dict(status='PASS',public_records=len(records),encoding_checks=tests,
                  field_degrees=[4,8],statement_sha256=hashlib.sha256(raw).hexdigest(),
                  scope='Retained public records only; variable-length tagged fingerprint/padding parity',
                  limits=['Not a source-trace extraction or natural bus-count adapter',
                          'Not a proof of the Python implementation or quantum security'])
    (directory/'bus-encoding-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
