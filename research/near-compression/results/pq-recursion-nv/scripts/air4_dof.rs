//! Single-cell perturbation sweep (lane/pq-nv-circuit-soundness FAITHFUL.md §V): every cell of
//! Sha512Air4, TableAir4 and the harness consumer, v -> v + d (d random non-zero), classified as
//! constraint / bus (exact multiset change of the windows containing the cell) / undetected.
use std::collections::{BTreeMap, HashMap};

use openvm_stark_backend::interaction::{BusIndex, Interaction, InteractionBuilder};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues};
use p3_baby_bear::BabyBear as F;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::{dense::RowMajorMatrixView, stack::VerticalPair};

use crate::air::*;
use crate::reference::Rng;
use crate::trace::gen_all;

pub struct WinEval<'a> {
    pub main: VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>,
    pub first: F,
    pub last: F,
    pub trans: F,
    pub bad: usize,
    pub ints: Vec<Interaction<F>>,
}
impl<'a> AirBuilder for WinEval<'a> {
    type F = F;
    type Expr = F;
    type Var = F;
    type M = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;
    fn main(&self) -> Self::M {
        self.main
    }
    fn is_first_row(&self) -> F {
        self.first
    }
    fn is_last_row(&self) -> F {
        self.last
    }
    fn is_transition_window(&self, _: usize) -> F {
        self.trans
    }
    fn assert_zero<I: Into<F>>(&mut self, x: I) {
        if x.into() != F::ZERO {
            self.bad += 1;
        }
    }
}
impl<'a> InteractionBuilder for WinEval<'a> {
    fn push_interaction<E: Into<F>>(&mut self, bus_index: BusIndex, fields: impl IntoIterator<Item = E>, count: impl Into<F>, count_weight: u32) {
        self.ints.push(Interaction { message: fields.into_iter().map(Into::into).collect(), count: count.into(), bus_index, count_weight });
    }
    fn num_interactions(&self) -> usize {
        self.ints.len()
    }
    fn all_interactions(&self) -> &[Interaction<F>] {
        &self.ints
    }
}
impl<'a> AirBuilderWithPublicValues for WinEval<'a> {
    type PublicVar = F;
    fn public_values(&self) -> &[F] {
        &[]
    }
}

type Key = (BusIndex, Vec<u32>);
fn add(acc: &mut HashMap<Key, F>, ints: &[Interaction<F>], s: F) {
    for it in ints {
        if it.count != F::ZERO {
            *acc.entry((it.bus_index, it.message.iter().map(|x| x.as_canonical_u32()).collect())).or_insert(F::ZERO) += s * it.count;
        }
    }
}

struct M {
    v: Vec<F>,
    w: usize,
    h: usize,
}
fn eval(air: usize, local: &[F], next: &[F], r: usize, h: usize) -> (usize, Vec<Interaction<F>>) {
    let mut b = WinEval {
        main: VerticalPair::new(RowMajorMatrixView::new_row(local), RowMajorMatrixView::new_row(next)),
        first: F::from_bool(r == 0),
        last: F::from_bool(r + 1 == h),
        trans: F::from_bool(r + 1 != h),
        bad: 0,
        ints: vec![],
    };
    match air {
        0 => Air::eval(&Sha512Air4, &mut b),
        1 => Air::eval(&TableAir4, &mut b),
        _ => Air::eval(&HarnessAir, &mut b),
    }
    (b.bad, b.ints)
}
fn rows(m: &M, x: usize) -> (&[F], &[F]) {
    let xn = (x + 1) % m.h;
    (&m.v[x * m.w..(x + 1) * m.w], &m.v[xn * m.w..(xn + 1) * m.w])
}

pub fn run(n_comp: usize) {
    let mut rng = Rng(0x5eed_0f_d0f ^ n_comp as u64);
    let comps: Vec<_> = (0..n_comp).map(|_| rng.comp()).collect();
    let t = gen_all(&comps);
    let to = |v: &[u32]| v.iter().map(|&x| F::from_u32(x)).collect::<Vec<F>>();
    let ms = [
        M { v: to(&t.main), w: WIDTH, h: t.main_height },
        M { v: to(&t.table), w: T_WIDTH, h: t.table.len() / T_WIDTH },
        M { v: to(&t.harness), w: H_WIDTH, h: t.harness_height },
    ];
    // honest global check
    let mut acc = HashMap::new();
    let mut bad = 0;
    for (a, m) in ms.iter().enumerate() {
        for r in 0..m.h {
            let (l, n) = rows(m, r);
            let (b, ints) = eval(a, l, n, r, m.h);
            bad += b;
            add(&mut acc, &ints, F::ONE);
        }
    }
    let unb = acc.values().filter(|v| **v != F::ZERO).count();
    println!("V4_DOF honest n={n_comp} main={}x{} bad={bad} unbalanced={unb}", ms[0].h, ms[0].w);
    assert_eq!((bad, unb), (0, 0));
    let mut rs = Rng(0xabcdef12345);
    let mut tally: BTreeMap<(usize, String, usize), [usize; 3]> = BTreeMap::new();
    let mut ex: BTreeMap<(usize, String, usize), usize> = BTreeMap::new();
    for (a, m) in ms.iter().enumerate() {
        for r in 0..m.h {
            let role = match a {
                0 if r >= n_comp * ROWS => "pad".to_string(),
                0 => format!("{:?}", kind_of(r % ROWS)),
                1 => "table".into(),
                _ => if r >= n_comp * 16 { "hpad".into() } else { "harness".into() },
            };
            for c in 0..m.w {
                let d = loop {
                    let v = (rs.next() % 2013265921) as u32;
                    if v != 0 {
                        break F::from_u32(v);
                    }
                };
                let mut wins = vec![r, (r + m.h - 1) % m.h];
                wins.dedup();
                let mut delta = HashMap::new();
                let mut b = 0;
                for &x in &wins {
                    let (l, n) = rows(m, x);
                    let (_, ints) = eval(a, l, n, x, m.h);
                    add(&mut delta, &ints, -F::ONE);
                    let (mut l2, mut n2) = (l.to_vec(), n.to_vec());
                    if x == r {
                        l2[c] += d;
                    }
                    if (x + 1) % m.h == r {
                        n2[c] += d;
                    }
                    let (bb, ints) = eval(a, &l2, &n2, x, m.h);
                    b += bb;
                    add(&mut delta, &ints, F::ONE);
                }
                let v = if b > 0 { 0 } else if delta.values().any(|v| *v != F::ZERO) { 1 } else { 2 };
                let k = (a, role.clone(), c);
                tally.entry(k.clone()).or_default()[v] += 1;
                if v == 2 {
                    ex.entry(k).or_insert(r);
                }
            }
        }
    }
    let mut tot = [0usize; 3];
    for ((a, role, c), t) in &tally {
        for i in 0..3 {
            tot[i] += t[i];
        }
        if t[2] > 0 {
            println!("V4_DOF_UNDETECTED air={a} role={role} col={c} {}/{} (e.g. row {})", t[2], t[0] + t[1] + t[2], ex[&(*a, role.clone(), *c)]);
        }
    }
    println!("V4_DOF_TOTAL n={n_comp} cells={} constraint={} bus={} undetected={}", tot[0] + tot[1] + tot[2], tot[0], tot[1], tot[2]);
}
