//! Assemble a full `nearAirV3` trace from per-table entry JSONs and prove it.
//!
//! Step 1 of the v3 prover: the *orchestration* that turns a set of per-table
//! entry lists (produced by the Lean witness→entries dumpers, or by the Rust
//! samplers) into the 25-table trace of `ZkFormal.NearV3.Assembly.nearAirV3`
//! and runs the v2 STARK prover (`prover::prove_cols_bytes`) at `auxGroup = 2`
//! with the prepared public tape (`v3::public::prepared_bytes`).
//!
//! Tables without honest entries yet can be supplied as a zero table of the
//! right width/height (they will fail non-local constraints; this is a plumbing
//! proof path, not yet a soundness-complete proof).  The load-bearing use is to
//! prove a trace built from real-witness entries and check it with the deployed
//! Lean verifier `np-lean-verify-v2`.

use crate::air::Air;
use crate::cols::TraceCols;

use super::Tab;
use super::collect;
use super::render;

/// Render table `t` (a name from [`super::TABLES`]) from its entry JSON, or a
/// zero table of width `w` and `log` rows when `json` is `None`/empty.
pub fn render_table(name: &str, json: Option<&str>, w: usize, log: usize) -> Result<Tab, String> {
    match json {
        Some(s) if !s.trim().is_empty() => render(name, s),
        _ => Ok(Tab::zero(log, w)),
    }
}

/// Add `sha_t`/`sha_r` to `entries` from the SHA collector when they are not
/// supplied: the two bins `TrieShaTwo.twoShaJobBins = [b0, b1]` of the four SHA
/// job families built from the other tables' entries ([`collect`]; the
/// `sha_scheduler`/`sha_receipt` entries stand in for absent ups/codec/rcpt
/// entries), so the `BYTES`/`DIGEST` buses balance as in `trie_side_exact`.
pub fn with_collected_sha(
    entries: &std::collections::HashMap<String, String>,
) -> Result<std::collections::HashMap<String, String>, String> {
    let mut out = entries.clone();
    let need_t = !entries.contains_key("sha_t");
    let need_r = !entries.contains_key("sha_r");
    if need_t || need_r {
        let (t, r) = collect::instances_from_entries(entries)?;
        if need_t {
            out.insert("sha_t".to_string(), t);
        }
        if need_r {
            out.insert("sha_r".to_string(), r);
        }
    }
    Ok(out)
}

/// Build the 25-table trace of `air` from a map `(table name → entries JSON)`.
/// Tables whose name is absent use a zero table of the AIR's width and a safe
/// log (`min(maxLog, 1)`, i.e. the minimum legal height).
pub fn traces_from_entries(
    air: &Air,
    entries: &std::collections::HashMap<String, String>,
) -> Result<Vec<TraceCols>, String> {
    // `NearAir.nearTablesFull` order ↔ the names this crate registers.
    const ORDER: &[&str] = &[
        "sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf",
        "codec", "scandist", "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size",
        "qv", "mrk", "sort",
    ];
    if air.tables.len() != ORDER.len() {
        return Err(format!(
            "air has {} tables, expected {} (nearAirV3)",
            air.tables.len(),
            ORDER.len()
        ));
    }
    let mut out = Vec::with_capacity(ORDER.len());
    for (t, name) in ORDER.iter().enumerate() {
        let tab = air.tables[t].clone();
        let w = tab.width;
        let log = 1usize.min(tab.max_log);
        let t2 = render_table(name, entries.get(*name).map(|s| s.as_str()), w, log)?;
        if t2.width != w {
            return Err(format!(
                "table {name}: rendered width {} != nearAirV3 width {w}",
                t2.width
            ));
        }
        if t2.log > tab.max_log {
            return Err(format!(
                "table {name}: rendered log {} > maxLog {}",
                t2.log, tab.max_log
            ));
        }
        out.push(TraceCols::from_matrix(&t2.to_matrix()));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Case-level assembly (`npudr v3prove <case_dir> <out_dir>`)
// ---------------------------------------------------------------------------

/// `NearAir.nearTablesFull` order ↔ the names this crate registers.
pub const ORDER: &[&str] = &[
    "sha_t", "sha_r", "node", "head", "val", "walk", "uniq", "ups", "chacha", "rng", "shuf",
    "codec", "scandist", "proc", "mem", "cmp", "rcpt", "acct", "akey", "bnd", "srcp", "size", "qv",
    "mrk", "sort",
];

/// The prover's inputs for one case: the hint, the prepared statement, its public tape
/// (`Public.preparedBytes p 0`, the STARK's claim bytes `cb'`) and the 25 entry JSONs.
pub struct CaseInputs {
    pub hint: super::prep::Hint,
    pub prep: super::prep::Prep,
    pub tape: Vec<u8>,
    pub entries: std::collections::HashMap<String, String>,
    /// `table name → where its entries came from` (`rust` / `lean-dump:<file>`).
    pub source: std::collections::BTreeMap<String, String>,
}

/// Build every table's honest entries for a real claim + witness: the native Rust
/// derivations (`v3::trie` for 2–7, 21; `v3::rcptfam` for 16–20, 23, 24; the SHA collector for
/// 0, 1) and, for the tables without a native port yet (8–15 scheduler/ChaCha, 22 qv), the entry
/// files of `extra` (`sched.json` for 11–15, `chacha.json`, `rng.json`, `shuf.json`, `qv.json`:
/// `np-lean-bundle-v3 <case> <extra>`).  A file `<extra>/<table>.json` also overrides any
/// native table (for differentials).
pub fn case_inputs(
    cb: &[u8],
    wb: &[u8],
    extra: Option<&std::path::Path>,
) -> Result<CaseInputs, String> {
    use std::collections::{BTreeMap, HashMap};
    let hint = super::hint::hint_of_e(cb, wb)?;
    let prep = super::d0::prep(cb, &hint)?;
    let tape = super::public::prepared_bytes(&prep, 0);
    let mut entries: HashMap<String, String> = HashMap::new();
    let mut source: BTreeMap<String, String> = BTreeMap::new();
    let tv = super::trie::entries(cb, wb)?;
    for t in ["node", "val", "head", "walk", "uniq", "ups", "size"] {
        let v = tv.get(t).ok_or(format!("v3trie: no table {t}"))?;
        entries.insert(t.into(), v.to_string());
        source.insert(t.into(), "rust:v3trie".into());
    }
    let f = super::rcptfam::rcpt_family(cb, wb)?;
    let js = |v: serde_json::Result<String>| v.map_err(|e| e.to_string());
    for (t, s) in [
        ("rcpt", js(serde_json::to_string(&f.rcpt))?),
        ("acct", js(serde_json::to_string(&f.acct))?),
        ("akey", js(serde_json::to_string(&f.akey))?),
        ("bnd", js(serde_json::to_string(&f.bnd))?),
        ("srcp", js(serde_json::to_string(&f.srcp))?),
        ("mrk", js(serde_json::to_string(&f.mrk))?),
        ("sort", js(serde_json::to_string(&f.sort))?),
    ] {
        entries.insert(t.into(), s);
        source.insert(t.into(), "rust:v3rcptfam".into());
    }
    if let Some(dir) = extra {
        let rd = |n: &str| std::fs::read_to_string(dir.join(n)).ok();
        if let Some(s) = rd("sched.json") {
            for t in ["codec", "scandist", "proc", "mem", "cmp"] {
                entries.insert(t.into(), s.clone());
                source.insert(t.into(), "lean-dump:sched.json".into());
            }
        }
        for (t, _) in super::TABLES {
            if let Some(s) = rd(&format!("{t}.json")) {
                entries.insert((*t).into(), s);
                source.insert((*t).into(), format!("lean-dump:{t}.json"));
            }
        }
    }
    let entries = with_collected_sha(&entries)?;
    for t in ["sha_t", "sha_r"] {
        source
            .entry(t.into())
            .or_insert_with(|| "rust:collect".into());
    }
    for t in ORDER {
        if !entries.contains_key(*t) {
            return Err(format!(
                "table {t}: no entries (native port missing; supply <extra>/{t}.json)"
            ));
        }
    }
    Ok(CaseInputs {
        hint,
        prep,
        tape,
        entries,
        source,
    })
}

/// Render table `name` straight into compact columns (the row-major [`Tab`] is dropped as
/// soon as the columns are filled).
pub fn render_cols(name: &str, json: &str) -> Result<TraceCols, String> {
    let t = render(name, json)?;
    let w = t.width;
    Ok(TraceCols::from_rows(t.log, w, |r, buf| {
        buf.copy_from_slice(&t.cells[r * w..(r + 1) * w])
    }))
}

/// One bus's balance: `(bus, #distinct messages, #units sent, #units received, imbalances)`.
pub struct BusBalance {
    pub bus: usize,
    pub msgs: usize,
    pub sent: u64,
    pub recv: u64,
    pub bad: Vec<crate::check::Imbalance>,
}

/// Exact balance of every bus of `air` over the 25 tables (compact columns) and the public
/// messages of the tape (`globalChecksP`: `∏sends·Π_pub(true) = ∏recvs·Π_pub(false)`, here as
/// multisets of `(bus, msg)`).  One bus at a time (bounded memory); `None` when the tape does
/// not fit (`pubFit`).
pub fn bus_balances(
    air: &Air,
    trs: &[TraceCols],
    pubs: &[crate::field::F],
    tape: &[u8],
) -> Option<Vec<BusBalance>> {
    use crate::air::{Expr, Tape};
    use crate::field::F;
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use rayon::prelude::*;
    use std::collections::{BTreeSet, HashMap};
    if !crate::verifier::pub_fit(air, tape) {
        return None;
    }
    let pm = crate::verifier::pub_msgs(air, tape);
    let mut buses: BTreeSet<usize> = air
        .tables
        .iter()
        .flat_map(|t| t.interactions.iter().map(|i| i.bus))
        .collect();
    buses.extend(pm.iter().map(|x| x.0));
    let mut out = vec![];
    for bus in buses {
        let mut m: HashMap<Vec<u32>, (u64, u64)> = HashMap::new();
        for (t, tr) in air.tables.iter().zip(trs) {
            let n = tr.height();
            for it in t.interactions.iter().filter(|it| it.bus == bus) {
                let exprs: Vec<Expr> = it.mult.iter().chain(&it.msg).cloned().collect();
                let tape = Tape::compile(&exprs);
                let nb = it.mult.len();
                const CH: usize = 1 << 16;
                for c0 in (0..n).step_by(CH) {
                    let part: Vec<(Vec<u32>, u64)> = (c0..(c0 + CH).min(n))
                        .into_par_iter()
                        .filter_map(|r| {
                            let mut regs = vec![];
                            let last = r + 1 == n;
                            tape.eval(
                                &mut regs,
                                |c, next| tr.get(if next { (r + 1) % n } else { r }, c),
                                pubs,
                                [
                                    F::from_bool(r == 0),
                                    F::from_bool(last),
                                    F::from_bool(!last),
                                ],
                            );
                            let o: Vec<F> =
                                tape.outputs.iter().map(|&k| regs[k as usize]).collect();
                            let mult: u64 = (0..nb)
                                .map(|k| if o[k] == F::ONE { 1u64 << k } else { 0 })
                                .sum();
                            (mult != 0).then(|| {
                                (o[nb..].iter().map(|x| x.as_canonical_u32()).collect(), mult)
                            })
                        })
                        .collect();
                    for (msg, k) in part {
                        let e = m.entry(msg).or_default();
                        if it.send { e.0 += k } else { e.1 += k }
                    }
                }
            }
        }
        for (b, send, rec) in &pm {
            if *b != bus {
                continue;
            }
            let e = m
                .entry(rec.iter().map(|x| x.as_canonical_u32()).collect())
                .or_default();
            if *send { e.0 += 1 } else { e.1 += 1 }
        }
        let (sent, recv) = m.values().fold((0, 0), |a, v| (a.0 + v.0, a.1 + v.1));
        let mut bad: Vec<crate::check::Imbalance> = m
            .iter()
            .filter(|(_, (s, r))| s != r)
            .map(|(msg, (s, r))| (bus, msg.clone(), *s, *r))
            .collect();
        bad.sort();
        out.push(BusBalance {
            bus,
            msgs: m.len(),
            sent,
            recv,
            bad,
        });
    }
    Some(out)
}

/// `ZkFormal.NearV3.Assembly.join h π = borshBytes h ++ π` (`HintCodec.lean`), `h = Hint.encode`.
pub fn join(hint: &[u8], pi: &[u8]) -> Vec<u8> {
    let mut v = crate::near::spec::borsh_bytes(hint);
    v.extend_from_slice(pi);
    v
}
