//! Honest SHA-256 trace generator for `nearAirV3` tables 0/1: the two `L5`
//! instances `ZkFormal.Sha.Table.table B_BYTES B_DIGEST`
//! (`NearV3/Assembly/NearAir.lean:42`).
//!
//! The v3 tables are the v1 table verbatim (`src/sha.rs`, already ported from
//! `ZkFormal/Near`'s `Sha.Gen`), so this module only exposes the existing
//! [`crate::sha::sha_cells`] through the [`super::render`] interface.
//!
//! Input: a JSON list of messages `{id, bytes, dmult}` (`bytes` is a list of
//! naturals `< 256`).  Output: the SHA table at width [`crate::sha::WIDTH`]
//! (544) and height `2^Gen.honestLog`, every cell reduced mod `P`.

use serde::Deserialize;

use crate::field::P;

use super::Tab;

/// The JSON mirror of [`crate::sha::Msg`] (`Gen.Msg`).
#[derive(Clone, Debug, Deserialize, serde::Serialize)]
pub struct ShaMsg {
    pub id: u32,
    #[serde(default)]
    pub bytes: Vec<u8>,
    /// whether the digest is provided on the digest bus (`Gen.Msg.dmult`)
    #[serde(default)]
    pub dmult: bool,
}

/// `Gen`'s SHA table as a [`Tab`] at `honestLog`, cells reduced mod `P`.
pub fn sha_aligned(msgs: &[ShaMsg]) -> Tab {
    let ms: Vec<crate::sha::Msg> = msgs
        .iter()
        .map(|m| crate::sha::Msg {
            id: m.id,
            bytes: m.bytes.clone(),
            dmult: m.dmult,
        })
        .collect();
    let (cells, _nrows, log) = crate::sha::sha_cells(&ms);
    Tab {
        log,
        width: crate::sha::WIDTH,
        cells: cells.iter().map(|&x| (x % P as u64) as u32).collect(),
    }
}

/// Parse `json` as a list of [`ShaMsg`] and render the SHA table.
pub fn render(json: &str) -> Result<Tab, String> {
    let msgs: Vec<ShaMsg> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(sha_aligned(&msgs))
}

/// `n` random messages (ids `1..`, `dmult`, lengths `0…64`) for `v3sample`.
pub fn sample(r: &mut super::sample::Rng, n: usize) -> Vec<ShaMsg> {
    (0..n.max(1))
        .map(|i| {
            let len = r.below(65) as usize;
            ShaMsg {
                id: i as u32 + 1,
                bytes: r.bytes(len).into_iter().map(|x| x as u8).collect(),
                dmult: true,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn matches_v1_sha_cells() {
        let msgs = crate::sha::toy_msgs(&[0, 1, 5, 64, 65]);
        let mirror: Vec<ShaMsg> = msgs
            .iter()
            .map(|m| ShaMsg {
                id: m.id,
                bytes: m.bytes.clone(),
                dmult: m.dmult,
            })
            .collect();
        let t = sha_aligned(&mirror);
        let (cells, nrows, log) = crate::sha::sha_cells(&msgs);
        assert_eq!(t.log, log);
        assert_eq!(t.width, crate::sha::WIDTH);
        assert_eq!(t.height(), 1usize << log);
        assert!(nrows <= t.height());
        let want: Vec<u32> = cells.iter().map(|&x| (x % P as u64) as u32).collect();
        assert_eq!(t.cells, want);
    }

    #[test]
    fn json_round_trip() {
        let mirror = vec![ShaMsg {
            id: 3,
            bytes: vec![1, 2, 3],
            dmult: true,
        }];
        let j = serde_json::to_string(&mirror).unwrap();
        let t = render(&j).unwrap();
        assert_eq!(t.width, crate::sha::WIDTH);
        assert_eq!(
            t.log,
            crate::sha::sha_cells(&[crate::sha::Msg {
                id: 3,
                bytes: vec![1, 2, 3],
                dmult: true,
            }])
            .2
        );
    }

    /// Every constraint of `nearAirV3` table 0 (and 1, identical) holds on the
    /// honest trace; the SHA tables read no public inputs.
    #[test]
    fn all_constraints_hold() {
        let air_json = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../conformance/out-v2/nearAirV3.json"
        );
        let txt = std::fs::read_to_string(air_json).expect("nearAirV3.json");
        let air = crate::air::Air::from_json(&txt).expect("parse air");
        let msgs = crate::sha::toy_msgs(&[0, 1, 5, 64, 65, 200]);
        let mirror: Vec<ShaMsg> = msgs
            .iter()
            .map(|m| ShaMsg {
                id: m.id,
                bytes: m.bytes.clone(),
                dmult: m.dmult,
            })
            .collect();
        let tab = sha_aligned(&mirror);
        let pubs = vec![crate::field::F::ZERO; air.num_pub];
        for idx in [0usize, 1] {
            let t = &air.tables[idx];
            assert_eq!(tab.width, t.width, "table {idx}");
            let bad = crate::check::failing_constraints(t, &tab.to_matrix(), &pubs, 40);
            assert!(bad.is_empty(), "table {idx} failing: {bad:?}");
        }
    }
}
