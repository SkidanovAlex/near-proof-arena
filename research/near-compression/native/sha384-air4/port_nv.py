"""Generate the NV crate copy of the v4 compression AIR from this crate's sources.

    python3 port_nv.py <openvm-sha384 tree>

writes crates/recursion/src/sha384/compress4_air.rs (from src/air.rs) and compress4_trace.rs
(from src/trace.rs) with fixed textual substitutions only: bus indices and the compression-id
offset become fields (as in compress2_air.rs), the AIRs take any AirBuilder, the test consumer
(HarnessAir) is dropped, and the native reference (Comp, sha2_compress, Words, Rng, ...) is the
NV crate's existing compress2_trace module.  The script fails if a pattern is missing.
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
tree = Path(sys.argv[1])
dst = tree / 'crates/recursion/src/sha384'


def sub(s, old, new, count=1):
    n = s.count(old)
    if n != count:
        raise SystemExit(f'pattern found {n} times (expected {count}): {old!r}')
    return s.replace(old, new)


air = (HERE / 'src/air.rs').read_text()
air = '//! (Generated from research/near-compression/native/sha384-air4/src/air.rs by port_nv.py:\n' \
      '//! bus indices and the compression-id offset are fields; no test consumer.)\n//!\n' + air
air = sub(air, 'use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};',
          'use p3_air::{Air, AirBuilder, BaseAir, BaseAirWithPublicValues};\npub use super::compress2_air::Sha2Buses;')
air = sub(air, '#![allow(clippy::needless_range_loop)]', '#![allow(clippy::needless_range_loop, dead_code)]')
COMPAT = '''
/// NV compatibility handle in place of v2.1's digit-width `Layout`: v4 has one layout (base-4
/// digits, limbs split at 21/42 bits = the NV k = 3 word format), so it only reports the
/// width and the degree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub width: usize,
}
impl Layout {
    pub fn new(k: usize) -> Self {
        assert_eq!(k, 3, "SHA AIR v4 emits the k = 3 word format (limbs split at 21/42 bits)");
        Layout { width: WIDTH }
    }
    pub fn degree(&self) -> usize {
        DEGREE
    }
}
/// Width of the test consumer's rows (gen_harness; the NV circuit uses GLUE instead).
pub const H_WIDTH: usize = 9;
'''
air = sub(air, '#[derive(Clone, Copy, Debug)]\npub struct Sha512Air4;',
          COMPAT + '\n#[derive(Clone, Copy, Debug)]\npub struct Sha512Air4 {\n    pub lay: Layout,\n    pub buses: Sha2Buses,\n    pub cid_offset: u32,\n}')
air = sub(air, '#[derive(Clone, Copy, Debug)]\npub struct TableAir4;',
          '#[derive(Clone, Copy, Debug)]\npub struct TableAir4 {\n    pub lay: Layout,\n    pub buses: Sha2Buses,\n}')
air = sub(air, 'impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for Sha512Air4',
          'impl<AB: AirBuilder + InteractionBuilder> Air<AB> for Sha512Air4')
air = sub(air, 'impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for TableAir4',
          'impl<AB: AirBuilder + InteractionBuilder> Air<AB> for TableAir4')
air = sub(air, 'push_interaction(BUS_CTL,', 'push_interaction(self.buses.ctl,', 2)
air = sub(air, 'push_interaction(BUS_K,', 'push_interaction(self.buses.k,', 2)
air = sub(air, 'push_interaction(BUS_IF, msg, count', 'push_interaction(self.buses.iface, msg, count')
air = sub(air, 'push_interaction(BUS_LB,', 'push_interaction(self.buses.lb,')
air = sub(air, 'let cid = g.clone() - r.clone();', 'let cid = g.clone() - r.clone() + c(self.cid_offset as u64);')
air = air[:air.index('/// Test consumer of the interface bus')].rstrip() + '\n'
(dst / 'compress4_air.rs').write_text(air)

tr = (HERE / 'src/trace.rs').read_text()
tr = sub(tr, '//! Trace generation for the SHA-512 compression AIR v4.\n',
         '//! Trace generation for the SHA-512 compression AIR v4.\n'
         '//! (Generated from research/near-compression/native/sha384-air4/src/trace.rs by port_nv.py.)\n')
tr = sub(tr, 'use crate::air::*;\nuse crate::air::Kind::*;\npub use crate::reference::*;',
         'use super::compress4_air::*;\nuse super::compress4_air::Kind::*;\n'
         'pub use super::compress2_trace::{\n    bsig0, bsig1, chf, majf, pad_message, round_words, sha2_compress, ssig0, ssig1, Comp, Rng, Words,\n'
         '    SHA384_IV, SHA512_IV,\n};')
(dst / 'compress4_trace.rs').write_text(tr)
print('wrote', dst / 'compress4_air.rs', dst / 'compress4_trace.rs')
