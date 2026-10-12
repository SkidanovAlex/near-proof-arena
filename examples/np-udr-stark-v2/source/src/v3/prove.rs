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

use super::collect;
use super::render;
use super::Tab;

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
