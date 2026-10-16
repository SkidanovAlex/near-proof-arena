#!/usr/bin/env python3
"""Prove real prepared-function diagnostic traces with the generic backend.

This is a bounded prepared-code AIR experiment, not a whole-Wasm/PREP theorem.
Uses the existing BLAKE2s diagnostic PCS, not the new SHA384 primitives.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import time

import native_folded_v2 as native
import prepared_function_air as machine
import scheduled_bus_whir as protocol
import scheduled_proof_codec_shared as codec


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('fixture',type=Path)
    ap.add_argument('native_examples',type=Path)
    ap.add_argument('output',type=Path)
    args=ap.parse_args();out=args.output.resolve();out.mkdir(exist_ok=False)
    def save(directory,name,value):
        p=directory/name;p.write_text(json.dumps(value,separators=(',',':'))+'\n');return p
    def generate(label,spec,rows,accept=True):
        started=time.monotonic();d=out/label;d.mkdir()
        def commit(name,values):
            source=save(d,name+'-rows.json',{'rows':values});target=d/(name+'-commitment.json')
            subprocess.run([str(args.native_examples.resolve()/'near_scheduled_commitment'),str(source),str(target),'--root-only'],check=True,stdout=subprocess.DEVNULL)
            return source,json.loads(target.read_text())['root']
        source,root=commit('source',rows)
        _,_,alpha,gamma=protocol.begin(spec,[root])
        witness=protocol.aux.generate(spec['air']['tables'][0],rows,spec['public'],alpha,gamma)
        coordinates=protocol.flatten_aux_rows(spec['air']['tables'][0],witness['aux_rows'],spec['log_rows'][0])
        auxiliary,aux_root=commit('aux',coordinates)
        proof,handoffs=native.prove(spec,[root],[rows],[aux_root],[witness['aux_rows']],[witness['finals']],protocol_impl=protocol)
        openings=[]
        for branch,path in enumerate((source,auxiliary)):
            h=save(d,f'handoff-{branch}.json',handoffs[0][branch]);target=d/f'opening-{branch}.json'
            subprocess.run([str(args.native_examples.resolve()/'near_scheduled_whir'),str(path),str(target),str(h)],check=True,stdout=subprocess.DEVNULL)
            openings.append(json.loads(target.read_text()))
        proof['tables'][0]['openings']=openings
        save(d,'proof.json',proof);save(d,'spec.json',spec);save(d,'statement.json',{'roots':[root]})
        blob=codec.encode(proof);(d/'proof.nsbpc').write_bytes(blob)
        decoded=codec.decode(blob)
        if decoded!=proof:raise ValueError('codec changed proof')
        try:protocol.verify(decoded,spec,[root])
        except ValueError as e:
            if accept:raise
            if 'zerocheck identity' not in str(e):raise
            return {'label':label,'fresh_committed_invalid_trace_rejected':True,'reason':str(e)}
        if not accept:raise ValueError('accepted invalid execution witness')
        return {'label':label,'status':'PASS','rows':len(rows),'columns':machine.WIDTH,
                'complete_binary_bytes':len(blob),'generation_and_verification_seconds':time.monotonic()-started}
    cases=json.loads(args.fixture.read_text())['cases'];reports=[]
    for case in cases:
        spec,rows=machine.make(case)
        reports.append(generate(case['label'],spec,rows))
        print(json.dumps(reports[-1]),flush=True)
    spec,rows=machine.make(cases[0]);bad=deepcopy(rows)
    bad[2][machine.STACK]^=1
    negative=generate('fresh-invalid-stack',spec,bad,False)
    result={'status':'PASS','cases':reports,'negative':negative,
            'scope':'Bounded public-prepared-code execution AIR with actual semantic fixtures.',
            'limitations':['No authenticated original-Wasm preparation or whole-machine refinement theorem.',
                           'Fixed16instruction/8i32stack bounds; const/add/drop/end only, no hosts.',
                           'Diagnostic BLAKE2s/BabyBearExt4 PCS; no128bitquantumsecurity claim.',
                           'No D3 receipt/action binding, fullNEAR or1Pgas claim.']}
    save(out,'verified.json',result)


if __name__=='__main__':main()
