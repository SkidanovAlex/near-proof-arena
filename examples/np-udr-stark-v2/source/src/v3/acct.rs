//! Honest `acct` trace generator for `nearAirV3` — STUB. Port the Lean generator
//! (`ZkFormal.NearV3....`) into `render(json) -> Result<Tab, String>`, mirroring the
//! pattern of `v3::node`. Registered in `v3::render` under the table name.

use crate::v3::Tab;

pub fn render(_json: &str) -> Result<Tab, String> {
    Err("acct: renderer not implemented yet (part 2 extension)".into())
}
