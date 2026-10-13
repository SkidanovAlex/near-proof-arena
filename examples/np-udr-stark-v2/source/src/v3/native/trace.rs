//! `PTrie.upsert` (`spec/lean/NearSpec/TrieUpsert.lean`) and its instrumented twin
//! `traceUpsert` (`zk-formal/ZkFormal/NearV3/Render/Ups/TreeTrace.lean`).
//!
//! Lean's `Kids` is a linked list of `nil` / `none` / `some` cells; here a branch's
//! children are a `Vec<Option<PTrie>>` of the same length and positions, so slot `n`
//! past the end is `Kids.nil` (the upsert fails there).
//!
//! All `memory_usage` arithmetic is Lean `Nat` (`u128` here; `a + b - c` truncates at 0).

use crate::near::spec::{PTrie, Slot, hex_prefix, is_prefix};

use super::{
    TreePart, TreeRun, UC_BI, UC_BR, UC_BV, UC_ESL0, UC_ESL1, UC_ESN0, UC_ESN1, UC_LP, UC_LSA,
    UC_LSB, UC_LSC, UK_MVE, UK_MVL, UK_NLF, UK_PT, UK_RBI, UK_RBR, UK_RBV, UK_RDB, UK_RDE, UK_RLP,
    UK_SPB, UK_WEX,
};

/// `Slot.len`.
fn slot_len(s: &Slot) -> u128 {
    match s {
        Slot::Val(v) => v.len() as u128,
        Slot::Ref(n, _) => *n,
    }
}

/// `PTrie.mem?`.
fn mem_opt(t: &PTrie) -> Option<u128> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(_, _, m) | PTrie::Ext(_, _, m) | PTrie::Branch(_, _, m) => Some(*m),
    }
}

/// `PTrie.memD`.
fn mem_d(t: &PTrie) -> u128 {
    mem_opt(t).unwrap_or(0)
}

/// `leafMem k vlen = 50 + 2·|hexPrefix k true| + (vlen + 50)`.
pub(crate) fn leaf_mem(k: &[u8], vlen: u128) -> u128 {
    50 + 2 * hex_prefix(k, true).len() as u128 + (vlen + 50)
}

/// `extOwnMem k = 50 + 2·|hexPrefix k false|`.
fn ext_own_mem(k: &[u8]) -> u128 {
    50 + 2 * hex_prefix(k, false).len() as u128
}

/// `valueMem vlen = vlen + 50`.
fn value_mem(vlen: u128) -> u128 {
    vlen + 50
}

/// `commonPrefix a b`.
fn common_prefix(a: &[u8], b: &[u8]) -> Vec<u8> {
    a.iter()
        .zip(b)
        .take_while(|(x, y)| x == y)
        .map(|(x, _)| *x)
        .collect()
}

/// `kidsFrom 16 0 f` for `kids1` / `kids2`: 16 slots, children at the given indices
/// (the first matching pair wins, as `if i = x … else if i = y …`).
fn kids16(cs: Vec<(u8, PTrie)>) -> Vec<Option<PTrie>> {
    let mut out: Vec<Option<PTrie>> = vec![None; 16];
    for (x, c) in cs.into_iter().rev() {
        if let Some(s) = out.get_mut(x as usize) {
            *s = Some(c);
        }
    }
    out
}

/// `kids1 x c`.
fn kids1(x: u8, c: PTrie) -> Vec<Option<PTrie>> {
    kids16(vec![(x, c)])
}

/// `kids2 x c y d`.
fn kids2(x: u8, c: PTrie, y: u8, d: PTrie) -> Vec<Option<PTrie>> {
    kids16(vec![(x, c), (y, d)])
}

/// `newLeaf k v`.
fn new_leaf(k: &[u8], v: &[u8]) -> PTrie {
    PTrie::Leaf(
        k.to_vec(),
        Slot::Val(v.to_vec()),
        leaf_mem(k, v.len() as u128),
    )
}

/// `wrapExt p b`.
fn wrap_ext(p: &[u8], b: PTrie) -> PTrie {
    if p.is_empty() {
        b
    } else {
        let m = ext_own_mem(p) + mem_d(&b);
        PTrie::Ext(p.to_vec(), Box::new(b), m)
    }
}

/// `splitLeaf k s key v`: the output of `leafSplitRun` (which builds exactly the
/// same tries, `wrapRun` = `wrapExt`; the leaf's `m` only enters the part sources).
fn split_leaf(k: &[u8], s: &Slot, key: &[u8], v: &[u8]) -> PTrie {
    split_leaf_run(k, s, 0, key, v).output
}

/// `splitExt k c m key v`.
fn split_ext(k: &[u8], c: &PTrie, m: u128, key: &[u8], v: &[u8]) -> PTrie {
    let p = common_prefix(k, key);
    let cm = m.saturating_sub(ext_own_mem(k));
    let Some((&x, xs)) = k[p.len()..].split_first() else {
        return PTrie::Ext(k.to_vec(), Box::new(c.clone()), m);
    };
    let (sub, sub_mem) = sub_of(xs, c, cm);
    let vl = v.len() as u128;
    match key[p.len()..].split_first() {
        None => wrap_ext(
            &p,
            PTrie::Branch(
                Some(Slot::Val(v.to_vec())),
                kids1(x, sub),
                50 + value_mem(vl) + sub_mem,
            ),
        ),
        Some((&y, ys)) => wrap_ext(
            &p,
            PTrie::Branch(
                None,
                kids2(x, sub, y, new_leaf(ys, v)),
                50 + sub_mem + leaf_mem(ys, vl),
            ),
        ),
    }
}

/// The moved extension below a split (`sub`, `subMem` of `splitExt` / `extSplitRun`).
fn sub_of(xs: &[u8], c: &PTrie, cm: u128) -> (PTrie, u128) {
    if xs.is_empty() {
        (c.clone(), cm)
    } else {
        let m = ext_own_mem(xs) + cm;
        (PTrie::Ext(xs.to_vec(), Box::new(c.clone()), m), m)
    }
}

/// `PTrie.upsert t key v` (with `Kids.upsert` inlined on the child vector).
pub(crate) fn upsert(t: &PTrie, key: &[u8], v: &[u8]) -> Option<PTrie> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(k, s, _) => Some(if k.as_slice() == key {
            new_leaf(k, v)
        } else {
            split_leaf(k, s, key, v)
        }),
        PTrie::Ext(k, c, m) => {
            if is_prefix(k, key) {
                let cm = mem_opt(c)?;
                let c2 = upsert(c, &key[k.len()..], v)?;
                let m2 = (m + mem_d(&c2)).saturating_sub(cm);
                Some(PTrie::Ext(k.clone(), Box::new(c2), m2))
            } else {
                Some(split_ext(k, c, *m, key, v))
            }
        }
        PTrie::Branch(bv, cs, m) => match key.split_first() {
            None => {
                let old = bv.as_ref().map(|s| value_mem(slot_len(s))).unwrap_or(0);
                let m2 = (m + value_mem(v.len() as u128)).saturating_sub(old);
                Some(PTrie::Branch(Some(Slot::Val(v.to_vec())), cs.clone(), m2))
            }
            Some((&n, rest)) => {
                // `Kids.upsert cs n rest v`
                let slot = cs.get(n as usize)?;
                let (child, old, new) = match slot {
                    None => (new_leaf(rest, v), 0, leaf_mem(rest, v.len() as u128)),
                    Some(c) => {
                        let cm = mem_opt(c)?;
                        let c2 = upsert(c, rest, v)?;
                        let nm = mem_d(&c2);
                        (c2, cm, nm)
                    }
                };
                let mut cs2 = cs.clone();
                cs2[n as usize] = Some(child);
                Some(PTrie::Branch(
                    bv.clone(),
                    cs2,
                    (m + new).saturating_sub(old),
                ))
            }
        },
    }
}

// ---------------------------------------------------------------------------
// `traceUpsert` (`Render/Ups/TreeTrace.lean`)
// ---------------------------------------------------------------------------

/// `TreePart.mk kind source output slot`.
fn part(kind: u8, source: &PTrie, output: PTrie, slot: u64) -> TreePart {
    TreePart {
        kind,
        source: source.clone(),
        output,
        slot,
    }
}

/// `pushPart run part`.
fn push_part(mut run: TreeRun, p: TreePart) -> TreeRun {
    run.output = p.output.clone();
    run.parts.push(p);
    run
}

/// `terminalRun src key cs matched result parts`.
fn terminal_run(
    src: &PTrie,
    key: &[u8],
    cs: u8,
    matched: usize,
    result: PTrie,
    parts: Vec<TreePart>,
) -> TreeRun {
    TreeRun {
        output: result,
        parts,
        terminal: cs,
        matched: matched as u64,
        terminal_source: src.clone(),
        terminal_key: key.to_vec(),
    }
}

/// `wrapRun src path run`.
fn wrap_run(src: &PTrie, path: &[u8], run: TreeRun) -> TreeRun {
    if path.is_empty() {
        run
    } else {
        let out = wrap_ext(path, run.output.clone());
        push_part(run, part(UK_WEX, src, out, 0))
    }
}

/// `leafSplitRun k s m key v` (`m` only enters `src`; `splitLeaf` passes any `m`).
fn split_leaf_run(k: &[u8], s: &Slot, m: u128, key: &[u8], v: &[u8]) -> TreeRun {
    let src = PTrie::Leaf(k.to_vec(), s.clone(), m);
    let p = common_prefix(k, key);
    let vl = v.len() as u128;
    let sl = slot_len(s);
    match (k[p.len()..].split_first(), key[p.len()..].split_first()) {
        (None, Some((&y, ys))) => {
            let fresh = new_leaf(ys, v);
            let branch = PTrie::Branch(
                Some(s.clone()),
                kids1(y, fresh.clone()),
                50 + value_mem(sl) + leaf_mem(ys, vl),
            );
            let parts = vec![
                part(UK_NLF, &src, fresh, 0),
                part(UK_SPB, &src, branch.clone(), 0),
            ];
            wrap_run(
                &src,
                &p,
                terminal_run(&src, key, UC_LSA, p.len(), branch, parts),
            )
        }
        (Some((&x, xs)), None) => {
            let moved = PTrie::Leaf(xs.to_vec(), s.clone(), leaf_mem(xs, sl));
            let branch = PTrie::Branch(
                Some(Slot::Val(v.to_vec())),
                kids1(x, moved.clone()),
                50 + value_mem(vl) + leaf_mem(xs, sl),
            );
            let parts = vec![
                part(UK_MVL, &src, moved, 0),
                part(UK_SPB, &src, branch.clone(), 0),
            ];
            wrap_run(
                &src,
                &p,
                terminal_run(&src, key, UC_LSB, p.len(), branch, parts),
            )
        }
        (Some((&x, xs)), Some((&y, ys))) => {
            let moved = PTrie::Leaf(xs.to_vec(), s.clone(), leaf_mem(xs, sl));
            let fresh = new_leaf(ys, v);
            let branch = PTrie::Branch(
                None,
                kids2(x, moved.clone(), y, fresh.clone()),
                50 + leaf_mem(xs, sl) + leaf_mem(ys, vl),
            );
            let parts = vec![
                part(UK_MVL, &src, moved, 0),
                part(UK_NLF, &src, fresh, 0),
                part(UK_SPB, &src, branch.clone(), 0),
            ];
            wrap_run(
                &src,
                &p,
                terminal_run(&src, key, UC_LSC, p.len(), branch, parts),
            )
        }
        (None, None) => {
            let nl = new_leaf(key, v);
            terminal_run(
                &src,
                key,
                UC_LP,
                key.len(),
                nl.clone(),
                vec![part(UK_RLP, &src, nl, 0)],
            )
        }
    }
}

/// `extSplitRun k c m key v`.
fn ext_split_run(k: &[u8], c: &PTrie, m: u128, key: &[u8], v: &[u8]) -> TreeRun {
    let src = PTrie::Ext(k.to_vec(), Box::new(c.clone()), m);
    let p = common_prefix(k, key);
    let cm = m.saturating_sub(ext_own_mem(k));
    let Some((&x, xs)) = k[p.len()..].split_first() else {
        return terminal_run(&src, key, UC_ESL1, p.len(), src.clone(), vec![]);
    };
    let (sub, sub_mem) = sub_of(xs, c, cm);
    let mut parts = if xs.is_empty() {
        vec![]
    } else {
        vec![part(UK_MVE, &src, sub.clone(), 0)]
    };
    let vl = v.len() as u128;
    match key[p.len()..].split_first() {
        None => {
            let branch = PTrie::Branch(
                Some(Slot::Val(v.to_vec())),
                kids1(x, sub),
                50 + value_mem(vl) + sub_mem,
            );
            parts.push(part(UK_SPB, &src, branch.clone(), 0));
            let cs = if xs.is_empty() { UC_ESL1 } else { UC_ESL0 };
            wrap_run(
                &src,
                &p,
                terminal_run(&src, key, cs, p.len(), branch, parts),
            )
        }
        Some((&y, ys)) => {
            let fresh = new_leaf(ys, v);
            let branch = PTrie::Branch(
                None,
                kids2(x, sub, y, fresh.clone()),
                50 + sub_mem + leaf_mem(ys, vl),
            );
            parts.push(part(UK_NLF, &src, fresh, 0));
            parts.push(part(UK_SPB, &src, branch.clone(), 0));
            let cs = if xs.is_empty() { UC_ESN1 } else { UC_ESN0 };
            wrap_run(
                &src,
                &p,
                terminal_run(&src, key, cs, p.len(), branch, parts),
            )
        }
    }
}

/// `qRDE k m c' cm = .ext k c' (m + c'.memD − cm)` (`Extract/Ups/QNodes.lean`).
fn q_rde(k: &[u8], m: u128, c2: PTrie, cm: u128) -> PTrie {
    let m2 = (m + mem_d(&c2)).saturating_sub(cm);
    PTrie::Ext(k.to_vec(), Box::new(c2), m2)
}

/// `KidsRun`.
struct KidsRun {
    output: Vec<Option<PTrie>>,
    old_mem: u128,
    new_mem: u128,
    inner: TreeRun,
    inserted: bool,
}

/// `traceKids source wholeKey cs n key v` (slot `n` of the child vector).
fn trace_kids(
    source: &PTrie,
    whole_key: &[u8],
    cs: &[Option<PTrie>],
    n: usize,
    key: &[u8],
    v: &[u8],
) -> Option<KidsRun> {
    let slot = cs.get(n)?;
    let (child, old_mem, new_mem, inner, inserted) = match slot {
        None => {
            let fresh = new_leaf(key, v);
            let inner = terminal_run(
                source,
                whole_key,
                UC_BI,
                0,
                fresh.clone(),
                vec![part(UK_NLF, source, fresh.clone(), 0)],
            );
            (fresh, 0, leaf_mem(key, v.len() as u128), inner, true)
        }
        Some(c) => {
            let cm = mem_opt(c);
            let run = trace_upsert(c, key, v);
            let (cm, run) = (cm?, run?);
            let nm = mem_d(&run.output);
            (run.output.clone(), cm, nm, run, false)
        }
    };
    let mut output = cs.to_vec();
    output[n] = Some(child);
    Some(KidsRun {
        output,
        old_mem,
        new_mem,
        inner,
        inserted,
    })
}

/// `traceUpsert t key v`.
pub(crate) fn trace_upsert(t: &PTrie, key: &[u8], v: &[u8]) -> Option<TreeRun> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(k, s, m) => {
            if k.as_slice() == key {
                let nl = new_leaf(k, v);
                Some(terminal_run(
                    t,
                    key,
                    UC_LP,
                    k.len(),
                    nl.clone(),
                    vec![part(UK_RLP, t, nl, 0)],
                ))
            } else {
                Some(split_leaf_run(k, s, *m, key, v))
            }
        }
        PTrie::Ext(k, c, m) => {
            if is_prefix(k, key) {
                let cm = mem_opt(c);
                let run = trace_upsert(c, &key[k.len()..], v);
                let (cm, run) = (cm?, run?);
                let kind = if k.is_empty() { UK_PT } else { UK_RDE };
                let out = q_rde(k, *m, run.output.clone(), cm);
                Some(push_part(run, part(kind, t, out, 0)))
            } else {
                Some(ext_split_run(k, c, *m, key, v))
            }
        }
        PTrie::Branch(bv, cs, m) => match key.split_first() {
            None => {
                let old = bv.as_ref().map(|s| value_mem(slot_len(s))).unwrap_or(0);
                let m2 = (m + value_mem(v.len() as u128)).saturating_sub(old);
                let result = PTrie::Branch(Some(Slot::Val(v.to_vec())), cs.clone(), m2);
                let (cs_, kind) = if bv.is_some() {
                    (UC_BR, UK_RBR)
                } else {
                    (UC_BV, UK_RBV)
                };
                Some(terminal_run(
                    t,
                    &[],
                    cs_,
                    0,
                    result.clone(),
                    vec![part(kind, t, result, 0)],
                ))
            }
            Some((&n, rest)) => {
                let kr = trace_kids(t, key, cs, n as usize, rest, v)?;
                let kind = if kr.inserted { UK_RBI } else { UK_RDB };
                let out = PTrie::Branch(
                    bv.clone(),
                    kr.output,
                    (m + kr.new_mem).saturating_sub(kr.old_mem),
                );
                Some(push_part(kr.inner, part(kind, t, out, n as u64)))
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `memory_usage` a canonical node should store, recomputed bottom-up.
    fn mem_check(t: &PTrie) -> u128 {
        let m = match t {
            PTrie::Hash(_) => return 0,
            PTrie::Leaf(k, s, _) => leaf_mem(k, slot_len(s)),
            PTrie::Ext(k, c, _) => ext_own_mem(k) + mem_check(c),
            PTrie::Branch(v, cs, _) => {
                50 + v.as_ref().map(|s| value_mem(slot_len(s))).unwrap_or(0)
                    + cs.iter().flatten().map(mem_check).sum::<u128>()
            }
        };
        assert_eq!(mem_d(t), m, "stored memory_usage of {t:?}");
        m
    }

    fn up(t: &PTrie, key: &[u8], v: &[u8]) -> (PTrie, TreeRun) {
        let run = trace_upsert(t, key, v).expect("trace");
        let u = upsert(t, key, v).expect("upsert");
        assert_eq!(run.output, u, "traceUpsert output = PTrie.upsert");
        mem_check(&u);
        (u, run)
    }

    #[test]
    fn leaf_replace_and_split() {
        let t = new_leaf(&[0, 1, 2], b"a");
        let (t1, r) = up(&t, &[0, 1, 2], b"bb");
        assert_eq!(t1, new_leaf(&[0, 1, 2], b"bb"));
        assert_eq!((r.terminal, r.matched), (UC_LP, 3));
        // two-sided split under an extension over the common prefix `[0]`
        let (t2, r) = up(&t, &[0, 3, 4], b"c");
        let kinds: Vec<u8> = r.parts.iter().map(|p| p.kind).collect();
        assert_eq!(kinds, vec![UK_MVL, UK_NLF, UK_SPB, UK_WEX]);
        assert_eq!((r.terminal, r.matched), (UC_LSC, 1));
        assert!(matches!(&t2, PTrie::Ext(k, _, _) if k == &vec![0]));
        // key ends at the split point: branch value
        let (_, r) = up(&t, &[0], b"d");
        assert_eq!(r.terminal, UC_LSB);
        let (_, r) = up(&t, &[0, 1, 2, 5], b"e");
        assert_eq!(r.terminal, UC_LSA);
    }

    #[test]
    fn branch_insert_ext_split_and_order_independence() {
        let keys: [&[u8]; 5] = [&[0, 15], &[0, 15, 1], &[1, 2, 3, 4], &[1, 2, 9], &[0, 3]];
        let mut a = new_leaf(keys[0], b"v0");
        for (i, k) in keys.iter().enumerate().skip(1) {
            a = up(&a, k, &[i as u8; 3]).0;
        }
        // the same map inserted in reverse order gives the same canonical trie
        let mut b = new_leaf(keys[4], &[4u8; 3]);
        for (i, k) in keys.iter().enumerate().rev().skip(1) {
            let v: Vec<u8> = if i == 0 {
                b"v0".to_vec()
            } else {
                vec![i as u8; 3]
            };
            b = up(&b, k, &v).0;
        }
        assert_eq!(a.hash_of(), b.hash_of());
        // branch slot insert (`BI`, `RBI` at slot 7)
        let (_, r) = up(&a, &[7, 7], b"x");
        assert_eq!(r.terminal, UC_BI);
        let last = r.parts.last().unwrap();
        assert_eq!((last.kind, last.slot), (UK_RBI, 7));
        // extension split (`[1,2]` → branch at nibble 2, sub-extension kept)
        let (_, r) = up(&a, &[1, 5], b"y");
        assert!(matches!(r.terminal, UC_ESN0 | UC_ESN1));
        // an unrevealed subtree on the path: no upsert
        let h = PTrie::Branch(None, vec![Some(PTrie::Hash(vec![1; 32]))], 50);
        assert!(upsert(&h, &[0, 1], b"z").is_none());
        assert!(trace_upsert(&h, &[0, 1], b"z").is_none());
        // slot past a short child list (`Kids.nil`)
        assert!(upsert(&h, &[3], b"z").is_none());
    }
}
