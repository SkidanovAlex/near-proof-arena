#!/usr/bin/env python3
"""Create an isolated candidate copy with explicit scheduler-height APIs.

Never modifies the input crate. Default public render entrypoints remain log22.
All active rows, proc tail, and at least one following padding row must fit.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import shutil


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate_source',type=Path)
    ap.add_argument('output_source',type=Path)
    args=ap.parse_args();source=args.candidate_source.resolve();output=args.output_source.resolve()
    if output.exists():raise SystemExit('Refusing existing output source: '+str(output))
    shutil.copytree(source,output,ignore=shutil.ignore_patterns('target','.git'))
    path=output/'src/v3/sched.rs';before=path.read_text();s=before
    old='''fn sched_tab(rows: &[Vec<u64>], width: usize, pad: impl Fn(usize) -> Option<Vec<u64>>) -> Tab {
    let mut t = Tab::zero(SCHED_LOG, width);
    let h = t.height();'''
    new='''fn sched_tab_at_log(rows: &[Vec<u64>], width: usize, pad: impl Fn(usize) -> Option<Vec<u64>>, log: usize) -> Tab {
    assert!((1..=22).contains(&log), "scheduler log must be within1..22");
    let h = 1usize << log;
    assert!(rows.len().checked_add(1).is_some_and(|n|n<=h), "scheduler active prefix plus padding exceeds height");
    assert!(rows.iter().all(|r|r.len()<=width), "scheduler active row width");
    let mut t = Tab::zero(log, width);'''
    assert s.count(old)==1;s=s.replace(old,new)
    s=s.replace('for (q, row) in rows.iter().enumerate().take(h) {','for (q, row) in rows.iter().enumerate() {',1)
    s=s.replace('''        if let Some(row) = pad(q) {
            for (c, &x) in row.iter().enumerate().take(width) {''','''        if let Some(row) = pad(q) {
            assert!(row.len()<=width, "scheduler padding row width");
            for (c, &x) in row.iter().enumerate() {''',1)
    s=s.replace('for (c, &x) in row.iter().enumerate().take(width) {','for (c, &x) in row.iter().enumerate() {',1)
    s=s.replace('for q in rows.len().min(h)..h {','for q in rows.len()..h {',1)
    declarations=[('cmp','cmps: &[(u64, u64, u64)]','cmps'),('mem','rs: &[&Run]','rs'),
                  ('proc','rs: &[&Run]','rs'),('scandist','bs: &[SchedIn]','bs'),('codec','bs: &[SchedIn]','bs')]
    for name,parameters,argument in declarations:
        old=f'pub fn {name}_aligned({parameters}) -> Tab {{'
        new=f'pub fn {name}_aligned({parameters}) -> Tab {{ {name}_aligned_at_log({argument}, SCHED_LOG) }}\n\npub fn {name}_aligned_at_log({parameters}, log: usize) -> Tab {{'
        assert s.count(old)==1;s=s.replace(old,new)
    for old,new in [
        ('sched_tab(&rows, CMP_WIDTH, |_| Some(pad.clone()))','sched_tab_at_log(&rows, CMP_WIDTH, |_| Some(pad.clone()), log)'),
        ('sched_tab(&rows, MEM_WIDTH, |_| None)','sched_tab_at_log(&rows, MEM_WIDTH, |_| None, log)'),
        ('sched_tab(&scandist_rows(bs), SCANDIST_WIDTH, |_| None)','sched_tab_at_log(&scandist_rows(bs), SCANDIST_WIDTH, |_| None, log)'),
        ('sched_tab(&rows, CODEC_WIDTH, |_| None)','sched_tab_at_log(&rows, CODEC_WIDTH, |_| None, log)'),
        ('    sched_tab(&rows, PROC_WIDTH, |q| {','''    assert!((1..=22).contains(&log), "proc log must be within1..22");
    assert!(n_rows.checked_add(2).is_some_and(|n|n<=(1usize<<log)), "proc prefix plus tail plus padding exceeds height");
    sched_tab_at_log(&rows, PROC_WIDTH, |q| {'''),
        ('''            pad.clone()
        })
    })''','''            pad.clone()
        })
    }, log)''')]:
        assert s.count(old)==1,(old,s.count(old));s=s.replace(old,new)
    s+='''
// Research-only explicit height APIs; existing entrypoints retain SCHED_LOG.
#[derive(serde::Serialize)]
pub struct HeightPlan { pub name: &'static str, pub planned: usize, pub tail: usize, pub required: usize }
pub fn height_plan(json: &str) -> Result<Vec<HeightPlan>, String> {
    let bs=parse_all(json)?;
    let counts=[("codec",bs.iter().map(|b|codec_block(b).0.len()).sum::<usize>(),0),
        ("scandist",scandist_rows(&bs).len(),0),
        ("proc",bs.iter().map(|b|proc_rows(&b.run).len()).sum::<usize>(),1),
        ("mem",bs.iter().map(|b|mem_rows(&b.run).len()).sum::<usize>(),0),
        ("cmp",cmp_requests(&bs).len(),0)];
    counts.into_iter().map(|(name,planned,tail)| {
        let required=planned.checked_add(tail).and_then(|n|n.checked_add(1)).ok_or("scheduler required rows overflow")?;
        Ok(HeightPlan{name,planned,tail,required})
    }).collect()
}
pub fn render_at_log(name: &str, json: &str, log: usize) -> Result<Tab,String> {
    if !(1..=22).contains(&log) { return Err("scheduler log must be within1..22".into()); }
    let plans=height_plan(json)?;
    let plan=plans.iter().find(|p|p.name==name).ok_or("unknown scheduler table")?;
    if plan.required>(1usize<<log) { return Err(format!("{} requires {} rows incl tail/pad, log{} cannot fit",name,plan.required,log)); }
    let bs=parse_all(json)?;let runs:Vec<_>=bs.iter().map(|b|&b.run).collect();
    Ok(match name {
        "codec"=>codec_aligned_at_log(&bs,log), "scandist"=>scandist_aligned_at_log(&bs,log),
        "proc"=>proc_aligned_at_log(&runs,log), "mem"=>mem_aligned_at_log(&runs,log),
        "cmp"=>cmp_aligned_at_log(&cmp_requests(&bs),log), _=>unreachable!(),
    })
}
'''
    path.write_text(s)
    here=Path(__file__).resolve().parent
    patch=''.join(difflib.unified_diff(before.splitlines(True),s.splitlines(True),fromfile='a/src/v3/sched.rs',tofile='b/src/v3/sched.rs'))
    (here/'d1-height-render.patch').write_text(patch)
    (here/'d1-height-source.json').write_text(json.dumps({'source':str(source),'isolated':str(output),
        'changed_file':'src/v3/sched.rs','before_sha256':hashlib.sha256(before.encode()).hexdigest(),
        'after_sha256':hashlib.sha256(s.encode()).hexdigest(),
        'patch_sha256':hashlib.sha256(patch.encode()).hexdigest(),
        'scope':'Explicit height wrappers in isolated copy; no production edits; no AIR changes.'},indent=2)+'\n')
    print(output)


if __name__=='__main__':main()
