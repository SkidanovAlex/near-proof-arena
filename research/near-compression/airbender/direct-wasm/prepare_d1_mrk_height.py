#!/usr/bin/env python3
"""Add explicit complete-block Merkle height API to the isolated height crate."""
import argparse,difflib,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('isolated_source',type=Path);a=p.parse_args()
f=a.isolated_source/'src/v3/mrksort.rs';before=f.read_text();s=before
old='pub fn mrk_aligned(v: &MrkV) -> Tab {\n    let n = v.n;'
new='''pub fn mrk_aligned(v: &MrkV) -> Tab { mrk_at_log(v, MRK_LOG).expect("default Merkle capacity") }

/// Complete root/node prefix plus one inactive row; never split hashed blocks.
pub fn mrk_required_rows(v: &MrkV) -> Result<usize,String> {
    if v.n == 0 {
        if !v.nodes.is_empty() { return Err("empty Merkle input has nodes".into()); }
        return Ok(2);
    }
    // Reject impossible counts before constructing the shape vector.
    if v.n > (1u64 << MRK_LOG) { return Err("Merkle count exceeds supported capacity".into()); }
    let shape=mrk_shape(v.n as usize);
    if shape.len()!=v.nodes.len() { return Err("Merkle node count differs from complete shape".into()); }
    let mut required=2usize; // root plus at least one inactive padding row
    for ((_,_,hashed),node) in shape.iter().zip(&v.nodes) {
        if *hashed != matches!(node,MrkNode::Hashed{..}) {
            return Err("Merkle node kind differs from complete shape".into());
        }
        required=required.checked_add(if *hashed {64} else {1}).ok_or("Merkle row capacity overflow")?;
    }
    Ok(required)
}

pub fn mrk_at_log(v: &MrkV, log: usize) -> Result<Tab,String> {
    if !(1..=MRK_LOG).contains(&log) { return Err("Merkle log must be within1..19".into()); }
    let required=mrk_required_rows(v)?;
    if required>(1usize<<log) { return Err(format!("Merkle requires {required} rows including padding, log{log} cannot fit")); }
    let n = v.n;'''
assert s.count(old)==1;s=s.replace(old,new)
start=s.index('pub fn mrk_at_log(');end=s.index('/// Parse `json`',start)
part=s[start:end].replace('return t;','return Ok(t);').replace('Tab::zero(MRK_LOG, MRK_V3_WIDTH)','Tab::zero(log, MRK_V3_WIDTH)')
part=part.replace("    'shape: for",'    for').replace('''        let nd = match v.nodes.get(k) {
            Some(nd) => nd,
            None => break,
        };''','''        let nd = &v.nodes[k];''').replace('''            if q >= h {
                break 'shape;
            }
''','').replace('    t\n}','    Ok(t)\n}')
s=s[:start]+part+s[end:];f.write_text(s)
here=Path(__file__).resolve().parent
patch=''.join(difflib.unified_diff(before.splitlines(True),s.splitlines(True),fromfile='a/src/v3/mrksort.rs',tofile='b/src/v3/mrksort.rs'))
(here/'d1-mrk-height.patch').write_text(patch)
(here/'d1-mrk-height-source.json').write_text(json.dumps({'changed_file':'src/v3/mrksort.rs','before_sha256':hashlib.sha256(before.encode()).hexdigest(),'after_sha256':hashlib.sha256(s.encode()).hexdigest(),'patch_sha256':hashlib.sha256(patch.encode()).hexdigest()},indent=2)+'\n')
