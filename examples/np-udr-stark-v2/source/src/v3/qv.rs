//! Honest `qvV3` trace generator for `nearAirV3` (table index 22, the repaired
//! `Qv.Candidates.KeyTrafficRepair.table`), the Rust twin of the Lean mixed
//! queue row generator `ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mixedRows`
//! (`Qv/Candidates/CombinedTrace.lean`): the read-plan walk rows
//! (`ws.flatMap Walk.rows`), then the value records (`ValueGen.recordsRows vs`),
//! padded to the aligned height `padLog22 (logOf (qvRows ws vs))`
//! (`Render/PaddedQv.lean`).  The repaired `KEYNIB` traffic only changes the
//! interactions, not the rows or the local constraints, so the honest rows are
//! the same as `CombinedTable`'s.
//!
//! Input: a JSON `{ "walks": [...], "records": [...] }` whose fields are the
//! Lean `Walk`/`Record` projections (`CombinedWalkGen.Walk`,
//! `ValueGen.Record` + `ByteBuffer`).  `conformance/run-v2.sh` compares the dump
//! with `np-lean-render-v3` byte for byte.

use serde::Deserialize;

use super::Tab;
use super::{b, get, log_of, pad_log22};

pub const QV_WIDTH: usize = 52;

/// `ValueGen.ValueTable.width`: the record row width (the walk row extends it).
pub const VALUE_WIDTH: usize = 37;

// ---------------------------------------------------------------------------
// JSON mirrors (`CombinedWalkGen.Walk`, `ValueGen.Record`/`ByteBuffer`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct QvItem {
    pub shard: Vec<u64>,
    pub index: Vec<u64>,
}

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct QvWalkIn {
    /// `Kind.code`: `0` delayed, `1` buffered, `2` yielded, `3` group.
    pub code: u64,
    /// `shard` of `Kind.group` (the last 8 bytes of `Kind.bytes`).
    pub shard: u64,
    pub tau: u64,
    pub slot: u64,
    pub count: u64,
    /// `Walk.value` (`None` → absent); only `isSome` matters for the rows.
    pub value: Option<Vec<u64>>,
    pub vid: u64,
    pub users: u64,
    #[serde(rename = "lastMain")]
    pub last_main: bool,
    #[serde(rename = "final")]
    pub fin: bool,
}

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct QvRecIn {
    /// `Payload` tag: `0` empty, `1` buffer, `2` raw.
    pub rkind: u64,
    pub vid: u64,
    pub tau: u64,
    pub users: u64,
    /// `Payload.empty` index (8 bytes).
    pub index: Vec<u64>,
    /// `Payload.buffer` entries (`ByteBuffer`).
    pub entries: Vec<QvItem>,
    /// `Payload.raw` bytes.
    pub bytes: Vec<u64>,
}

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct QvIn {
    pub walks: Vec<QvWalkIn>,
    pub records: Vec<QvRecIn>,
}

// ---------------------------------------------------------------------------
// Walk rows (`CombinedWalkGen.Walk.row` / `Kind.bytes` / `Walk.mode`)
// ---------------------------------------------------------------------------

/// `Kind.bytes`: `[7] | [13] | [10] | [16] ++ u64 shard`.
fn kind_bytes(code: u64, shard: u64) -> Vec<u64> {
    match code {
        0 => vec![7],
        1 => vec![13],
        2 => vec![10],
        _ => {
            let mut v = vec![16];
            v.extend(u64_bytes(shard));
            v
        }
    }
}

/// `kind.code`: the inductive tag.
fn kind_code(k: &QvWalkIn) -> u64 {
    k.code
}

/// `Walk.mode w` (`ValueTable` mode column, `2` for non-main rows).
fn walk_mode(k: &QvWalkIn) -> u64 {
    if k.tau == 0 {
        match k.code {
            1 => 1,
            3 => 2,
            _ => 0,
        }
    } else {
        2
    }
}

/// `ValueGen.row cfg pos byte phase subpos entry regs` (37 cells).
#[allow(clippy::too_many_arguments)]
fn value_row(
    vid: u64,
    tau: u64,
    users: u64,
    mode: u64,
    length: u64,
    count: u64,
    pos: u64,
    byte: u64,
    phase: u64,
    subpos: u64,
    entry: u64,
    regs: &[u64],
) -> [u64; VALUE_WIDTH] {
    let last = b(length == 0 || pos + 1 == length);
    let zero = b(length == 0);
    let mut r = [0u64; VALUE_WIDTH];
    r[0] = 1;
    r[1] = b(pos == 0);
    r[2] = last;
    r[3] = vid;
    r[4] = length;
    r[5] = pos;
    r[6] = byte;
    r[7] = users;
    r[8] = tau;
    r[9] = entry;
    r[10] = count;
    r[11] = zero;
    r[12] = b(zero == 0);
    r[13] = b(last == 0);
    r[14] = b(mode == 0);
    r[15] = b(mode == 1);
    r[16] = b(mode == 2);
    r[17] = b(phase == 0);
    r[18] = b(phase == 1);
    r[19] = b(phase == 2);
    r[20] = b(phase == 3);
    for i in 0..8usize {
        r[21 + i] = b(phase != 4 && subpos == i as u64);
    }
    for i in 0..8usize {
        r[29 + i] = get(regs, i);
    }
    r
}

/// `wordRows cfg offset phase entry bytes regs`.
fn word_rows(
    vid: u64,
    tau: u64,
    users: u64,
    mode: u64,
    length: u64,
    count: u64,
    offset: u64,
    phase: u64,
    entry: u64,
    bytes: &[u64],
    regs: &[u64],
) -> Vec<[u64; VALUE_WIDTH]> {
    bytes
        .iter()
        .enumerate()
        .map(|(i, &bb)| {
            value_row(
                vid,
                tau,
                users,
                mode,
                length,
                count,
                offset + i as u64,
                bb,
                phase,
                i as u64,
                entry,
                regs,
            )
        })
        .collect()
}

/// `CombinedWalkGen.Walk.row w pos byte` (52 cells).
fn walk_row(k: &QvWalkIn, kb: &[u64], pos: u64, byte: u64) -> [u64; QV_WIDTH] {
    let code = kind_code(k);
    let mode = walk_mode(k);
    let has_value = k.value.is_some();
    let vid = if has_value { k.vid } else { 0 };
    let bits: Vec<u64> = (0..8).map(|i| (byte >> i) & 1).collect();
    let base = value_row(vid, k.tau, k.users, 2, 0, k.count, 0, 0, 4, 0, 0, &bits);
    let mut r = [0u64; QV_WIDTH];
    r[..VALUE_WIDTH].copy_from_slice(&base);
    r[4] = mode;
    let first = pos == 0;
    let last = pos + 1 == kb.len() as u64;
    let present = last && has_value;
    let main = k.tau == 0;
    r[37] = 1;
    r[38] = code % 2;
    r[39] = code / 2;
    r[40] = pos;
    r[41] = byte;
    r[42] = k.slot;
    r[43] = b(first);
    r[44] = b(last);
    r[45] = b(last && k.fin);
    r[46] = b(!has_value);
    r[47] = b(code == 3 && !first);
    r[48] = b(present && main && code == 1);
    r[49] = b(main);
    r[50] = b(k.last_main);
    r[51] = b(present);
    r
}

/// `Walk.rows w = w.kind.bytes.zipIdx.map ...`.
fn walk_rows(k: &QvWalkIn) -> Vec<[u64; QV_WIDTH]> {
    let kb = kind_bytes(k.code, k.shard);
    kb.iter()
        .enumerate()
        .map(|(i, &byte)| walk_row(k, &kb, i as u64, byte))
        .collect()
}

// ---------------------------------------------------------------------------
// Record rows (`ValueGen.{emptyRows,bufferRows,rawRows}` / `Record.size`)
// ---------------------------------------------------------------------------

/// `ValueGen.emptyRows vid tau users index`.
fn empty_rows(vid: u64, tau: u64, users: u64, index: &[u64]) -> Vec<[u64; VALUE_WIDTH]> {
    let mut rows = word_rows(vid, tau, users, 0, 16, 0, 0, 2, 0, index, index);
    rows.extend(word_rows(vid, tau, users, 0, 16, 0, 8, 3, 0, index, index));
    rows
}

/// `ValueGen.bufferRows vid tau users es`.
fn buffer_rows(vid: u64, tau: u64, users: u64, es: &[QvItem]) -> Vec<[u64; VALUE_WIDTH]> {
    let n = es.len() as u64;
    let length = 4 + 24 * n;
    let head = u32_bytes(n);
    let mut rows = word_rows(vid, tau, users, 1, length, n, 0, 0, 0, &head, &head);
    for (i, e) in es.iter().enumerate() {
        let i = i as u64;
        rows.extend(word_rows(
            vid,
            tau,
            users,
            1,
            length,
            n,
            4 + 24 * i,
            1,
            i,
            &e.shard,
            &e.index,
        ));
        rows.extend(word_rows(
            vid,
            tau,
            users,
            1,
            length,
            n,
            12 + 24 * i,
            2,
            i,
            &e.index,
            &e.index,
        ));
        rows.extend(word_rows(
            vid,
            tau,
            users,
            1,
            length,
            n,
            20 + 24 * i,
            3,
            i,
            &e.index,
            &e.index,
        ));
    }
    rows
}

/// `ValueGen.rawRows vid tau users bytes`.
fn raw_rows(vid: u64, tau: u64, users: u64, bytes: &[u64]) -> Vec<[u64; VALUE_WIDTH]> {
    if bytes.is_empty() {
        vec![value_row(vid, tau, users, 2, 0, 0, 0, 0, 4, 0, 0, &[])]
    } else {
        bytes
            .iter()
            .enumerate()
            .map(|(i, &bb)| {
                value_row(
                    vid,
                    tau,
                    users,
                    2,
                    bytes.len() as u64,
                    0,
                    i as u64,
                    bb,
                    4,
                    0,
                    0,
                    &[],
                )
            })
            .collect()
    }
}

/// `ValueGen.Record.rows`.
fn record_rows(v: &QvRecIn) -> Vec<[u64; VALUE_WIDTH]> {
    match v.rkind {
        0 => empty_rows(v.vid, v.tau, v.users, &v.index),
        1 => buffer_rows(v.vid, v.tau, v.users, &v.entries),
        _ => raw_rows(v.vid, v.tau, v.users, &v.bytes),
    }
}

/// `ValueGen.Record.size` (the row count of a valid record).
fn record_size(v: &QvRecIn) -> u64 {
    match v.rkind {
        0 => 16,
        1 => 4 + 24 * v.entries.len() as u64,
        _ => (v.bytes.len() as u64).max(1),
    }
}

// ---------------------------------------------------------------------------
// Little-endian helpers (`NearSpec.u32`/`u64`)
// ---------------------------------------------------------------------------

fn u32_bytes(n: u64) -> Vec<u64> {
    vec![
        n % 256,
        (n / 256) % 256,
        (n / 65536) % 256,
        (n / 16777216) % 256,
    ]
}

fn u64_bytes(n: u64) -> Vec<u64> {
    (0..8).map(|i| (n >> (8 * i)) % 256).collect()
}

// ---------------------------------------------------------------------------
// The aligned trace
// ---------------------------------------------------------------------------

/// `qvRows ws vs = (ws.flatMap Walk.rows).length + recordsSize vs`.
fn qv_rows(ws: &[QvWalkIn], vs: &[QvRecIn]) -> u64 {
    ws.iter()
        .map(|w| kind_bytes(w.code, w.shard).len() as u64)
        .sum::<u64>()
        + vs.iter().map(record_size).sum::<u64>()
}

/// Build the honest `qvV3` trace at the aligned height.
pub fn qv_aligned(q: &QvIn) -> Tab {
    let total = qv_rows(&q.walks, &q.records);
    let log = pad_log22(log_of(total as usize));
    let mut t = Tab::zero(log, QV_WIDTH);
    let h = t.height() as u64;
    let mut pos: u64 = 0;
    let emit = |row: &[u64], pos: &mut u64, t: &mut Tab| {
        if *pos < h {
            for (c, &x) in row.iter().enumerate() {
                t.set(*pos as usize, c, x);
            }
        }
        *pos += 1;
    };
    'outer: for w in &q.walks {
        for row in walk_rows(w) {
            if pos >= h {
                break 'outer;
            }
            emit(&row, &mut pos, &mut t);
        }
    }
    'recs: for v in &q.records {
        for row in record_rows(v) {
            if pos >= h {
                break 'recs;
            }
            emit(&row, &mut pos, &mut t);
        }
    }
    t
}

/// Parse `json` as a [`QvIn`] and render the aligned trace.
pub fn render(json: &str) -> Result<Tab, String> {
    let q: QvIn = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(qv_aligned(&q))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v3::sample::Rng;

    #[test]
    fn walk_and_record_rows() {
        let mut r = Rng::new(4);
        let q = crate::v3::sample::qv(&mut r, 3);
        let t = qv_aligned(&q);
        assert_eq!(t.width, QV_WIDTH);
        assert!(t.height() as u64 >= qv_rows(&q.walks, &q.records));
        // first row is the first byte of the first walk: walk flag, tau = 0
        assert_eq!(t.cells[0], 1);
        assert_eq!(t.cells[37], 1);
    }
}
