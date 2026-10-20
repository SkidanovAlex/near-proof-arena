//! FORGING hooks (spike only; tools/perf-design/forge). A dishonest prover that commits a trace
//! violating the AIR and still emits a proof, so that the *verifier* must reject it.
//! * `NPUDR_FORGE=1`: skip the prover's own checks (global ALI/bus check and the final-FRI-layer
//!   degree check: the final polynomial is then interpolated from two points), naive forgery.
//! * `NPUDR_FORGE=2`: additionally rewrite the first quotient chunk's OOD value of every table so
//!   that the verifier's ALI identity at `z` holds (the quotient openings then disagree with the
//!   committed quotient: the DEEP/FRI phase must catch it).
//! * `NPUDR_FORGE_BUS=1`: rewrite one receive-group final so that the global bus products balance
//!   (combine with `NPUDR_FORGE=2` to also patch the resulting ALI failure at `z`).
use p3_field::{Field, PrimeCharacteristicRing};

use crate::air::{Air, Tape};
use crate::aux::{AuxLayout, aux_constraints};
use crate::field::{EF, F};
use crate::protocol::Schedule;
use crate::verifier::{Challenges, ood_offsets, pub_msgs, pub_prod, selectors};

pub fn mode() -> u32 {
    std::env::var("NPUDR_FORGE").ok().and_then(|v| v.parse().ok()).unwrap_or(0)
}

pub fn balance_finals(air: &Air, finals: &mut [EF], cb: &[u8], alpha: EF, gamma: EF) {
    if std::env::var("NPUDR_FORGE_BUS").ok().as_deref() != Some("1") {
        return;
    }
    let (mut s, mut r) = (EF::ONE, EF::ONE);
    let mut off = 0;
    let mut last_recv = None;
    for t in &air.tables {
        let lay = AuxLayout::new(t, air.aux_group);
        for g in 0..lay.num_finals() {
            if g < lay.send_groups {
                s *= finals[off + g];
            } else {
                r *= finals[off + g];
                last_recv = Some(off + g);
            }
        }
        off += lay.num_finals();
    }
    let pm = pub_msgs(air, cb);
    s *= pub_prod(&pm, alpha, gamma, true);
    r *= pub_prod(&pm, alpha, gamma, false);
    if let Some(i) = last_recv {
        finals[i] *= s * r.inverse();
        eprintln!("[forge] receive final {i} rewritten to balance the bus products");
    }
}

pub fn fix_ood(air: &Air, sch: &Schedule, ood: &mut [EF], finals: &[EF], ch: &Challenges, pubs: &[F]) {
    if mode() < 2 {
        return;
    }
    let offs = ood_offsets(sch);
    let mut foff = 0;
    let mut fixed = 0;
    for t in 0..sch.num_tables() {
        let tab = &air.tables[t];
        let lay = AuxLayout::new(tab, air.aux_group);
        let (w, wa) = (sch.w_main[t], sch.w_aux[t]);
        let o = offs[t];
        let fins = &finals[foff..foff + sch.n_finals[t]];
        foff += sch.n_finals[t];
        let v: Vec<EF> = ood[o..o + sch.ood_len(t)].to_vec();
        let (zh, sel) = selectors(ch.z, sch.heights[t]);
        let col = |c: usize, n: bool| if n { v[w + c] } else { v[c] };
        let tape = Tape::compile(&tab.constraints);
        let mut regs = vec![];
        tape.eval::<EF>(&mut regs, col, pubs, sel);
        let mut cs: Vec<EF> = tape.outputs.iter().map(|&x| regs[x as usize]).collect();
        let mut iregs = vec![];
        lay.itape.eval::<EF>(&mut iregs, col, pubs, sel);
        let ivals: Vec<EF> = lay.itape.outputs.iter().map(|&x| iregs[x as usize]).collect();
        let mut phis = vec![];
        aux_constraints(tab, &lay, &ivals, ch.alpha_fp, ch.gamma_mul, &v[2 * w..2 * w + wa], &v[2 * w + wa..2 * w + 2 * wa], fins, sel, &mut cs, &mut phis);
        let mut acc = EF::ZERO;
        let mut ap = EF::ONE;
        for c in &cs {
            acc += ap * *c;
            ap *= ch.alpha_c;
        }
        let qoff = 2 * w + 2 * wa;
        let zt = ch.z.exp_power_of_2(sch.heights[t]);
        let mut q = EF::ZERO;
        let mut zp = EF::ONE;
        for j in 0..sch.n_quot[t] {
            q += zp * v[qoff + j];
            zp *= zt;
        }
        if acc != zh * q {
            ood[o + qoff] += acc * zh.inverse() - q;
            fixed += 1;
        }
    }
    eprintln!("[forge] OOD quotient values rewritten for {fixed} table(s)");
}
