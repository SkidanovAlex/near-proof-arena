//! Reader for the Lean-dumped per-table entry lists (part 2c).
//!
//! `np-lean-entries-v3` writes JSON arrays of the Lean entry structures with the
//! same nested-tagged encoding that `src/v3` deserializes (the Lean `ToJson`
//! mirrors the `FromJson` `np-lean-render-v3` consumes).  This module parses such
//! a list into the typed entry structs and exposes the parse so the honest
//! generators ([`super::render`], [`super::node::node_aligned`]) can run on
//! real-witness- derived entries, not just the random samplers.
//!
//! `npudr v3entries <table> <entries.json>` prints a one-line summary (entry
//! count and total serialized bytes), a fast smoke test that the dump is
//! well-formed; rendering and constraint checking go through the existing
//! `v3render` / `v3check`.

use serde::de::DeserializeOwned;

use super::node::NodeS3;
use super::*;

/// Parse a Lean entry dump for `table` into the typed entries.
pub fn parse<T: DeserializeOwned>(json: &str) -> Result<Vec<T>, String> {
    serde_json::from_str(json).map_err(|e| e.to_string())
}

/// Entry count and (for `node`) total serialized bytes of a dump.
pub fn describe(table: &str, json: &str) -> Result<String, String> {
    match table {
        "bnd" => Ok(format!("{} bnd entries", parse::<BndE>(json)?.len())),
        "akey" => Ok(format!("{} akey entries", parse::<AkeyE>(json)?.len())),
        "head" => Ok(format!("{} head entries", parse::<HeadE>(json)?.len())),
        "val" => Ok(format!("{} val entries", parse::<ValE>(json)?.len())),
        "uniq" => Ok(format!("{} uniq entries", parse::<UEnt>(json)?.len())),
        "walk" => Ok(format!("{} walk entries", parse::<WalkR>(json)?.len())),
        "node" => {
            let vs = parse::<NodeS3>(json)?;
            let bytes: usize = vs.iter().map(|s| s.v.ser_len()).sum();
            Ok(format!(
                "{} node entries, {bytes} serialized bytes",
                vs.len()
            ))
        }
        t => Err(format!("unknown table {t}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v3::sample::Rng;

    #[test]
    fn round_trips_sampler_dumps() {
        let mut r = Rng::new(11);
        let j = serde_json::to_string(&sample::node(&mut r, 4)).unwrap();
        assert_eq!(parse::<NodeS3>(&j).unwrap().len(), 4);
        assert!(describe("node", &j).unwrap().contains("4 node entries"));
        assert_eq!(
            parse::<HeadE>(&serde_json::to_string(&sample::head(&mut r, 2)).unwrap())
                .unwrap()
                .len(),
            2
        );
        assert!(describe("bogus", "[]").is_err());
    }
}
