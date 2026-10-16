"""Exercise the proved Lean call checker on an actual retained DAG selection."""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
from certify_sha384_occurrence_chains import frame


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--dag-directory',type=Path,required=True)
    p.add_argument('--fixture-directory',type=Path,required=True)
    p.add_argument('--output-directory',type=Path,required=True)
    a=p.parse_args();src=a.fixture_directory;out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    selection=json.loads((src/'selection.json').read_text())
    config=json.loads((src/'config.json').read_text())
    calls=json.loads((a.dag_directory/'hash-call-map.json').read_text())
    rows=json.loads((src/'source-03-rows.json').read_text())['rows'][:len(config['uses'])]
    assert [r[2] for r in rows]==config['uses']
    cases=[];cursor=0
    for index in selection['actual_call_indices']:
        call=calls[index];nodes=call['nodes'];message=frame(call)
        assert hashlib.sha384(message).hexdigest()==call['digest_hex']
        assert config['uses'][cursor:cursor+len(nodes)]==nodes
        blocks=[config['nodes'][node-config['base']][8:136] for node in nodes]
        final=config['nodes'][nodes[-1]-config['base']][136:]
        cases.append(dict(name=f'call-{index}',rows=rows,message=list(message),ordinals=list(range(cursor,cursor+len(nodes))),blocks=blocks,final=final,expected=True))
        cursor+=len(nodes)
    assert cursor==len(rows)
    baseline=next(c for c in cases if len(c['ordinals'])>=2)
    def mutate(name,edit):
        case=copy.deepcopy(baseline);case.update(name=name,expected=False);edit(case);cases.append(case)
    mutate('wrong-IV',lambda c:c['rows'][c['ordinals'][0]].__setitem__(3,c['rows'][c['ordinals'][0]][3]^1))
    mutate('hidden-output-word',lambda c:c['rows'][c['ordinals'][0]].__setitem__(127,c['rows'][c['ordinals'][0]][127]^1))
    mutate('hidden-input-word',lambda c:c['rows'][c['ordinals'][1]].__setitem__(31,c['rows'][c['ordinals'][1]][31]^1))
    mutate('block-word',lambda c:c['rows'][c['ordinals'][0]].__setitem__(35,c['rows'][c['ordinals'][0]][35]^1))
    mutate('operand-byte',lambda c:c['message'].__setitem__(0,c['message'][0]^1))
    mutate('padding-length',lambda c:c['blocks'][-1].__setitem__(127,c['blocks'][-1][127]^1))
    mutate('missing-block',lambda c:(c['ordinals'].pop(),c['blocks'].pop()))
    mutate('reordered-uses',lambda c:c['ordinals'].reverse())
    mutate('out-of-range-use',lambda c:c['ordinals'].__setitem__(0,len(rows)))
    mutate('wrong-final',lambda c:c['final'].__setitem__(0,c['final'][0]^1))
    mutate('short-block',lambda c:c['blocks'][0].pop())
    fixture=out/'cases.json';fixture.write_text(json.dumps(cases,separators=(',',':'))+'\n')
    package=Path(__file__).resolve().parents[2]
    result=subprocess.run(['lake','env','lean','--run','CheckSHA384ChunkCalls.lean',str(fixture.resolve())],cwd=package,text=True,capture_output=True,check=False)
    (out/'lean.log').write_text(result.stdout+result.stderr)
    result.check_returncode()
    counts=json.loads(result.stdout.strip().splitlines()[-1]);assert counts==dict(status='PASS',accepted=len(selection['actual_call_indices']),rejected=11)
    report=dict(**counts,call_indices=selection['actual_call_indices'],compression_steps=cursor,
        negative_cases=[c['name'] for c in cases if not c['expected']],
        files={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in [fixture,src/'config.json',src/'selection.json',src/'source-03-rows.json',a.dag_directory/'hash-call-map.json',package/'CheckSHA384ChunkCalls.lean',package/'NearCompression/SHA384ChunkCallCheck.lean']},
        scope='Lean checker establishes canonical blocks/padding, IV, full512-bit state links and final state for supplied message bytes and ordered-use rows. Compression AIR validity, commitment binding, transcript operand provenance and recursive arithmetization remain separate; no new recursive proof or security claim.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(counts))

if __name__=='__main__':main()
