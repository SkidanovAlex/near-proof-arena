"""Canonicality checks for the shadow-only response encoding candidate."""
import json
import screen_response_transcript as s


def main():
    values = [[], [{'leaf': [0, s.h.P-1], 'path': ['ab'*48]}],
              [{'values': [[0]*8, [1]*8], 'path': []}],
              [[{'leaf': [1, 2], 'path': ['00'*48]}]]]
    checks = 0
    for value in values:
        wire = s.encode(value)
        assert s.decode(wire) == value
        for bad in [wire[:-1], wire+b'x', b'X'+wire[1:]]:
            try: s.decode(bad)
            except (ValueError, AssertionError): checks += 1
            else: raise AssertionError('accepted malformed wire')
    for value in [True, -1, s.h.P, {'leaf': [], 'path': ['AB'*48]},
                  {'leaf': [], 'path': [], 'extra': 0}]:
        try: s.encode(value)
        except (AssertionError, ValueError): checks += 1
        else: raise AssertionError('accepted noncanonical input')
    print(json.dumps(dict(status='PASS', roundtrips=len(values), negative_cases=checks,
                          scope='Encoding checks only; no protocol or security certificate.')))


if __name__ == '__main__': main()
