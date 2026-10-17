//! Coverage-tiered challenges (contracts v1.7, docs/CONTRACTS.md §11,
//! docs/BENCHMARK_SPEC.md §17; first user `near-chunk-v3`).
//!
//! A coverage-tiered challenge has one statement (`statement_spec`) and a
//! total order of tiers. A candidate declares the tier it is complete for
//! (`candidate.toml [entry] declared_tier`), is admitted under that tier's
//! `params`, may abstain (`prove` exit 3, `UNSUPPORTED`) outside it, and is
//! ranked by tier rank first, then by score.

use crate::challenge::ChallengeDefinition;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const COVERAGE_VERSION: &str = "coverage-v1";

/// `prove` exit code meaning `UNSUPPORTED` (abstain: the witness is outside
/// the declared tier). Only meaningful on challenges with `coverage`.
pub const PROVE_EXIT_UNSUPPORTED: i32 = 3;

/// `ChallengeDefinition.coverage`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageSpec {
    /// `"coverage-v1"`.
    pub version: String,
    /// Lean declaration of the top `ChallengeSpec` (the statement every
    /// admitted verifier is sound for), e.g. `NearSpecV3.challengeSpecChunkTop`.
    pub statement_spec: String,
    /// Trusted Lean lemma lifting tier soundness to the statement, e.g.
    /// `NearSpecV3.sound_lift`.
    pub soundness_lift: String,
    /// Tiers in any order; `rank` is the total order (higher = larger domain).
    pub tiers: Vec<CoverageTier>,
    /// `succinct` badge thresholds (v1.9, BENCHMARK_SPEC §17). Serialized only
    /// when present, so ids of challenges without the badge are unchanged.
    /// Display-only: not a gate and not a score component.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub succinct: Option<SuccinctSpec>,
}

/// Thresholds of the `succinct` badge (BENCHMARK_SPEC §17; proposal for
/// `near-chunk-v3`: 2 MiB and 50 ms).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct SuccinctSpec {
    /// Largest accepted proof over the conformance and held-out runs.
    pub max_proof_bytes: u64,
    /// Largest verify wall time over the conformance and held-out runs.
    pub max_verify_ns: u64,
    /// Log-log slope test (§17): fitted exponent of proof bytes and of verify
    /// time against the case's total gas must be ≤ 0.1 (`exponent_bound_ppm`),
    /// with a 95% upper confidence bound ≤ `ucb_bound_ppm` ppm of the same
    /// quantity (proposal: 0.25 = 250,000 ppm).
    #[serde(default, skip_serializing_if = "is_default_u32")]
    pub exponent_bound_ppm: u32,
    #[serde(default, skip_serializing_if = "is_default_u32")]
    pub ucb_bound_ppm: u32,
}

fn is_default_u32(v: &u32) -> bool {
    *v == 0
}

impl SuccinctSpec {
    pub fn exponent_bound_ppm(&self) -> u32 {
        if self.exponent_bound_ppm == 0 {
            100_000
        } else {
            self.exponent_bound_ppm
        }
    }

    pub fn ucb_bound_ppm(&self) -> u32 {
        if self.ucb_bound_ppm == 0 {
            250_000
        } else {
            self.ucb_bound_ppm
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageTier {
    /// Tier id, e.g. `D0`, `D1`, `D2`, `D3a`.
    pub id: String,
    pub rank: u32,
    /// Lean declaration (term) of the tier's `ChallengeParams`, e.g.
    /// `NearSpecV3.challengeParamsChunk .d0`. The judge's per-tier Expected
    /// template (formal-checker config `tiers`) instantiates exactly this.
    pub params: String,
    /// Workload classes this tier is complete for: an abstention on a
    /// positive case of one of them is `COVERAGE_GAP_IN_TIER`.
    pub classes: Vec<String>,
}

fn is_tier_id(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 32
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.')
}

impl CoverageSpec {
    pub fn tier(&self, id: &str) -> Option<&CoverageTier> {
        self.tiers.iter().find(|t| t.id == id)
    }

    /// Structural checks against the challenge it belongs to.
    pub fn validate(&self, chal: &ChallengeDefinition) -> Result<(), String> {
        if self.version != COVERAGE_VERSION {
            return Err(format!("coverage.version must be {COVERAGE_VERSION:?}"));
        }
        if self.statement_spec.is_empty() || self.soundness_lift.is_empty() {
            return Err("coverage.statement_spec and soundness_lift are required".into());
        }
        if self.tiers.is_empty() {
            return Err("coverage.tiers is empty".into());
        }
        let classes: Vec<&str> = chal
            .workload_suite
            .classes
            .iter()
            .map(|c| c.id.as_str())
            .collect();
        let mut ids = std::collections::BTreeSet::new();
        let mut ranks = std::collections::BTreeSet::new();
        for t in &self.tiers {
            if !is_tier_id(&t.id) {
                return Err(format!(
                    "coverage tier id {:?} is not [A-Za-z0-9._-]{{1,32}}",
                    t.id
                ));
            }
            if !ids.insert(t.id.as_str()) {
                return Err(format!("duplicate coverage tier {:?}", t.id));
            }
            if !ranks.insert(t.rank) {
                return Err(format!("duplicate coverage tier rank {}", t.rank));
            }
            if t.params.is_empty() {
                return Err(format!("coverage tier {:?} has no params", t.id));
            }
            for c in &t.classes {
                if !classes.contains(&c.as_str()) {
                    return Err(format!(
                        "coverage tier {:?} lists unknown workload class {c:?}",
                        t.id
                    ));
                }
            }
        }
        // A larger domain is complete for at least the classes of a smaller one.
        let mut by_rank: Vec<&CoverageTier> = self.tiers.iter().collect();
        by_rank.sort_by_key(|t| t.rank);
        for w in by_rank.windows(2) {
            if let Some(c) = w[0].classes.iter().find(|c| !w[1].classes.contains(c)) {
                return Err(format!(
                    "coverage tier {:?} (rank {}) omits class {c:?} of lower tier {:?}",
                    w[1].id, w[1].rank, w[0].id
                ));
            }
        }
        Ok(())
    }
}

/// Per-class tally of positive cases.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ClassCoverage {
    pub cases: u32,
    /// Proved and accepted by `verify`.
    pub proven: u32,
    /// `prove` answered `UNSUPPORTED`.
    pub abstained: u32,
}

/// One case set (conformance or held-out).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageSection {
    /// Keyed by workload class id; public fixtures without a class are
    /// tallied under [`FIXTURES_KEY`] (not a class: excluded from `share_ppm`).
    pub per_class: BTreeMap<String, ClassCoverage>,
    /// Weight-averaged proven fraction over the challenge's workload classes,
    /// in parts per million (contracts carry no floating point).
    pub share_ppm: u32,
}

pub const FIXTURES_KEY: &str = "public-fixtures";

/// Report field `coverage` (CONTRACTS §11).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageReport {
    /// The declared tier.
    pub tier: String,
    /// Public fixtures and judge-sampled cases.
    pub conformance: CoverageSection,
    /// Committed held-out cases (absent when the worker ran none).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub heldout: Option<CoverageSection>,
}

/// Held-out coverage as it may be **published** (CONTRACTS §11, covert
/// channel): aggregate counts and the weight-averaged share only — never the
/// per-class breakdown. Per-class held-out abstention counts are chosen by
/// the candidate and would leak a few bits per class about the secret inputs.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct HeldoutAggregate {
    pub cases: u32,
    /// Accepted by `verify`.
    pub proven: u32,
    /// `prove` answered `UNSUPPORTED`.
    pub abstained: u32,
    /// Weight-averaged proven fraction over the held-out classes with cases,
    /// in parts per million (as stored; not recomputed here).
    pub share_ppm: u32,
}

impl HeldoutAggregate {
    /// Aggregate a held-out section over its per-class counts. `None` when
    /// there is no held-out section.
    pub fn of_section(section: &CoverageSection) -> Option<Self> {
        Some(Self {
            cases: section.per_class.values().map(|c| c.cases).sum(),
            proven: section.per_class.values().map(|c| c.proven).sum(),
            abstained: section.per_class.values().map(|c| c.abstained).sum(),
            share_ppm: section.share_ppm,
        })
    }
}

/// The published form of [`CoverageReport`]: conformance in full (public
/// fixtures and public workload classes), held-out aggregate-only.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoveragePublic {
    /// The declared tier.
    pub tier: String,
    /// Public fixtures and judge-sampled cases.
    pub conformance: CoverageSection,
    /// Committed held-out cases, aggregate only (absent when the worker ran
    /// none). CONTRACTS §11 covert-channel mitigation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub heldout: Option<HeldoutAggregate>,
}

impl CoveragePublic {
    pub fn of_report(report: &CoverageReport) -> Self {
        Self {
            tier: report.tier.clone(),
            conformance: report.conformance.clone(),
            heldout: report
                .heldout
                .as_ref()
                .and_then(HeldoutAggregate::of_section),
        }
    }
}

impl CoverageSection {
    /// Record one positive case outcome.
    pub fn record(&mut self, class: Option<&str>, proven: bool, abstained: bool) {
        let e = self
            .per_class
            .entry(class.unwrap_or(FIXTURES_KEY).to_string())
            .or_default();
        e.cases += 1;
        e.proven += u32::from(proven);
        e.abstained += u32::from(abstained);
    }

    /// Recompute `share_ppm` from `per_class` and the challenge's class weights:
    /// `Σ_c w_c · proven_c / cases_c` over classes with cases, renormalized by
    /// the weight of those classes.
    pub fn finish(&mut self, chal: &ChallengeDefinition) {
        let mut num = 0u128;
        let mut den = 0u128;
        for c in &chal.workload_suite.classes {
            if let Some(x) = self.per_class.get(&c.id).filter(|x| x.cases > 0) {
                num += c.weight_ppm as u128 * x.proven as u128 * 1_000_000 / x.cases as u128;
                den += c.weight_ppm as u128;
            }
        }
        self.share_ppm = num.checked_div(den).map_or(0, |x| x as u32);
    }
}

/// Renormalize weights (ppm) to sum exactly 1_000_000 (largest remainder,
/// ties by position). `None` if every weight is 0.
pub fn renormalize_ppm(weights: &[u32]) -> Option<Vec<u32>> {
    let total: u64 = weights.iter().map(|&w| w as u64).sum();
    if total == 0 {
        return None;
    }
    let mut out: Vec<u32> = weights
        .iter()
        .map(|&w| (w as u64 * 1_000_000 / total) as u32)
        .collect();
    let mut rem: Vec<(u64, usize)> = weights
        .iter()
        .enumerate()
        .map(|(i, &w)| ((w as u64 * 1_000_000) % total, i))
        .collect();
    rem.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    let short = 1_000_000 - out.iter().map(|&w| w as u64).sum::<u64>();
    for (_, i) in rem.into_iter().take(short as usize) {
        out[i] += 1;
    }
    Some(out)
}

/// The classes a candidate proved, with weights renormalized over them
/// (BENCHMARK_SPEC §17: abstained classes carry no time and are excluded from
/// the score). `None` if no class was proved.
pub fn proven_classes(classes: &[crate::ClassMeasurement]) -> Option<Vec<crate::ClassMeasurement>> {
    let kept: Vec<crate::ClassMeasurement> =
        classes.iter().filter(|c| !c.abstained).cloned().collect();
    let w = renormalize_ppm(&kept.iter().map(|c| c.weight_ppm).collect::<Vec<_>>())?;
    Some(
        kept.into_iter()
            .zip(w)
            .map(|(mut c, w)| {
                c.weight_ppm = w;
                c
            })
            .collect(),
    )
}

// ---- `succinct` badge (BENCHMARK_SPEC §17; CONTRACTS §11) ------------------

/// One measured evaluation of the badge criteria ("recorded per run").
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct SuccinctBadge {
    /// Both the thresholds and both slope tests passed (fail-closed: a fit
    /// that cannot be computed denies the badge).
    pub granted: bool,
    /// Largest proof over the measured runs (`ClassMeasurement.proof_bytes_max`).
    pub max_proof_bytes: u64,
    /// Largest per-run Σ verify wall ns of a class's batch over the measured
    /// runs (cost_v1's paid quantity; ≥ any single proof's verify wall).
    pub max_verify_ns: u64,
    /// Log-log slope of proof bytes against per-run batch gas, in ppm of the
    /// exponent (0.137 → 137_000). `None` without gas data or spread.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bytes_exponent_ppm: Option<i64>,
    /// 95% upper confidence bound of the bytes exponent, ppm.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bytes_ucb_ppm: Option<i64>,
    /// Log-log slope of verify time against per-run batch gas, ppm.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verify_exponent_ppm: Option<i64>,
    /// 95% upper confidence bound of the verify exponent, ppm.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verify_ucb_ppm: Option<i64>,
    /// Why the badge was denied (empty when granted).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub denied: Vec<String>,
}

/// Minimum fit points and spread for the slope test: below these the fit is
/// degenerate and the badge is denied (fail-closed).
const SLOPE_MIN_POINTS: usize = 4;
/// The gas axis must span at least one doubling (`ln 2`) for a growth test.
const SLOPE_MIN_LN_SPAN: f64 = std::f64::consts::LN_2;

/// Evaluate the `succinct` badge of a coverage-tiered challenge over the
/// benchmark's measured classes (BENCHMARK_SPEC §17). `None` when the
/// challenge defines no thresholds. Abstained classes carry no timings and
/// are excluded (§17).
impl CoverageSpec {
    pub fn evaluate_succinct(&self, classes: &[crate::ClassMeasurement]) -> Option<SuccinctBadge> {
        let spec = self.succinct.as_ref()?;
        let proved: Vec<&crate::ClassMeasurement> =
            classes.iter().filter(|c| !c.abstained).collect();
        let max_proof_bytes = proved.iter().map(|c| c.proof_bytes_max).max().unwrap_or(0);
        let max_verify_ns = proved
            .iter()
            .flat_map(|c| c.verify_runs_ns.iter())
            .copied()
            .chain(proved.iter().map(|c| c.verify_median_ns))
            .max()
            .unwrap_or(0);
        let mut badge = SuccinctBadge {
            granted: false,
            max_proof_bytes,
            max_verify_ns,
            bytes_exponent_ppm: None,
            bytes_ucb_ppm: None,
            verify_exponent_ppm: None,
            verify_ucb_ppm: None,
            denied: vec![],
        };
        if max_proof_bytes > spec.max_proof_bytes {
            badge.denied.push(format!(
                "max proof {} > {} bytes",
                max_proof_bytes, spec.max_proof_bytes
            ));
        }
        if max_verify_ns > spec.max_verify_ns {
            badge.denied.push(format!(
                "max verify {} > {} ns",
                max_verify_ns, spec.max_verify_ns
            ));
        }
        // Per-run batch sums: x = Σ case gas, y = Σ proof bytes / Σ verify ns.
        // Points without a gas axis cannot enter a growth test.
        let mut pts: Vec<(f64, f64, f64)> = vec![];
        for c in &proved {
            for (&g, (&b, &v)) in c
                .gas_runs
                .iter()
                .zip(c.proof_bytes_runs.iter().zip(c.verify_runs_ns.iter()))
            {
                if g == 0 || b == 0 || v == 0 {
                    continue;
                }
                pts.push((g as f64, b as f64, v as f64));
            }
        }
        let gas_span = pts
            .iter()
            .map(|(g, _, _)| g.ln())
            .fold((f64::INFINITY, f64::NEG_INFINITY), |(lo, hi), x| {
                (lo.min(x), hi.max(x))
            });
        if pts.len() >= SLOPE_MIN_POINTS && gas_span.1 - gas_span.0 >= SLOPE_MIN_LN_SPAN {
            let bytes_fit =
                loglog_slope_ucb(&pts.iter().map(|(g, b, _)| (*g, *b)).collect::<Vec<_>>());
            let verify_fit =
                loglog_slope_ucb(&pts.iter().map(|(g, _, v)| (*g, *v)).collect::<Vec<_>>());
            for (label, fit) in [("bytes", bytes_fit), ("verify", verify_fit)] {
                match fit {
                    Some((exp, ucb)) => {
                        let (exp_ppm, ucb_ppm) = (to_ppm(exp), to_ppm(ucb));
                        match label {
                            "bytes" => {
                                badge.bytes_exponent_ppm = Some(exp_ppm);
                                badge.bytes_ucb_ppm = Some(ucb_ppm);
                            }
                            _ => {
                                badge.verify_exponent_ppm = Some(exp_ppm);
                                badge.verify_ucb_ppm = Some(ucb_ppm);
                            }
                        }
                        if exp_ppm > spec.exponent_bound_ppm() as i64 {
                            badge.denied.push(format!(
                                "{label} exponent {} ppm > {} ppm",
                                exp_ppm,
                                spec.exponent_bound_ppm()
                            ));
                        }
                        if ucb_ppm > spec.ucb_bound_ppm() as i64 {
                            badge.denied.push(format!(
                                "{label} exponent 95% UCB {} ppm > {} ppm",
                                ucb_ppm,
                                spec.ucb_bound_ppm()
                            ));
                        }
                    }
                    None => badge.denied.push(format!("{label} slope test has no fit")),
                }
            }
        } else {
            badge.denied.push(format!(
                "slope test needs ≥ {SLOPE_MIN_POINTS} gas-bearing runs spanning one doubling \
                 (have {} over {:.3} ln-units)",
                pts.len(),
                if gas_span.1.is_finite() {
                    gas_span.1 - gas_span.0
                } else {
                    0.0
                }
            ));
        }
        badge.granted = badge.denied.is_empty();
        Some(badge)
    }
}

fn to_ppm(x: f64) -> i64 {
    // Quantize an exponent to ppm; clamp to a sane range so rounding of huge
    // slopes cannot overflow.
    (x * 1_000_000.0).round().clamp(-1e15, 1e15) as i64
}

/// Ordinary-least-squares slope of `ln y` against `ln x` with its 95% upper
/// confidence bound (Student-t, `n - 2` dof). `None` when the design is
/// degenerate (fewer than 3 points, or zero residual spread).
fn loglog_slope_ucb(pts: &[(f64, f64)]) -> Option<(f64, f64)> {
    let n = pts.len();
    if n < 3 {
        return None;
    }
    let (sx, sy) = pts
        .iter()
        .fold((0.0, 0.0), |(a, b), (x, y)| (a + x.ln(), b + y.ln()));
    let (mx, my) = (sx / n as f64, sy / n as f64);
    let mut sxx = 0.0;
    let mut sxy = 0.0;
    for (x, y) in pts {
        let dx = x.ln() - mx;
        sxx += dx * dx;
        sxy += dx * (y.ln() - my);
    }
    if sxx <= 0.0 {
        return None;
    }
    let slope = sxy / sxx;
    let mut sse = 0.0;
    for (x, y) in pts {
        let e = y.ln() - my - slope * (x.ln() - mx);
        sse += e * e;
    }
    if n < 3 {
        return None;
    }
    let dof = (n - 2) as f64;
    let s2 = sse / dof;
    // s2 == 0 (perfect fit, e.g. identical y) leaves no finite CI; treat an
    // exactly-zero-residual fit with a nonnegligible slope honestly: the UCB
    // is the slope itself.
    let se = if s2 > 0.0 { (s2 / sxx).sqrt() } else { 0.0 };
    let t = if se > 0.0 {
        student_t_95_upper(dof)
    } else {
        0.0
    };
    Some((slope, slope + t * se))
}

/// 95th percentile of Student-t with `dof` degrees of freedom, via the
/// inverse of the incomplete beta function (bisection on a monotone CDF).
fn student_t_95_upper(dof: f64) -> f64 {
    // CDF(t) = 1 - 0.5 * I_{ν/(ν+t²)}(ν/2, 1/2) for t ≥ 0; CDF = 0.95
    // ⇔ I_x(ν/2, 1/2) = 0.10 with t² = ν(1 - x)/x.
    let a = dof / 2.0;
    let target = 0.10;
    let (mut lo, mut hi) = (1e-12, 1.0);
    for _ in 0..200 {
        let mid = 0.5 * (lo + hi);
        if inc_beta(mid, a, 0.5) > target {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let x = 0.5 * (lo + hi);
    (dof * (1.0 - x) / x).sqrt()
}

/// Regularized incomplete beta I_x(a, b) (continued fraction, Numerical
/// Recipes §6.4), for a, b > 0 and 0 < x < 1.
fn inc_beta(x: f64, a: f64, b: f64) -> f64 {
    let lbeta = ln_gamma(a + b) - ln_gamma(a) - ln_gamma(b) + a * x.ln() + b * (1.0 - x).ln();
    if x < (a + 1.0) / (a + b + 2.0) {
        betacf(x, a, b) * lbeta.exp() / a
    } else {
        1.0 - betacf(1.0 - x, b, a) * lbeta.exp() / b
    }
}

fn betacf(x: f64, a: f64, b: f64) -> f64 {
    const MAXIT: usize = 300;
    const EPS: f64 = 3.0e-16;
    const FPMIN: f64 = 1.0e-300;
    let qab = a + b;
    let qap = a + 1.0;
    let qam = a - 1.0;
    let mut c = 1.0;
    let mut d = 1.0 - qab * x / qap;
    if d.abs() < FPMIN {
        d = FPMIN;
    }
    d = 1.0 / d;
    let mut h = d;
    for m in 1..=MAXIT {
        let m2 = 2 * m;
        let mut aa = m as f64 * (b - m as f64) * x / ((qam + m2 as f64) * (a + m2 as f64));
        d = 1.0 + aa * d;
        if d.abs() < FPMIN {
            d = FPMIN;
        }
        c = 1.0 + aa / c;
        if c.abs() < FPMIN {
            c = FPMIN;
        }
        d = 1.0 / d;
        h *= d * c;
        aa = -(a + m as f64) * (qab + m as f64) * x / ((a + m2 as f64) * (qap + m2 as f64));
        d = 1.0 + aa * d;
        if d.abs() < FPMIN {
            d = FPMIN;
        }
        c = 1.0 + aa / c;
        if c.abs() < FPMIN {
            c = FPMIN;
        }
        d = 1.0 / d;
        let del = d * c;
        h *= del;
        if (del - 1.0).abs() < EPS {
            break;
        }
    }
    h
}

/// ln Γ (Lanczos), for the incomplete beta's normalizing constant.
fn ln_gamma(z: f64) -> f64 {
    const G: f64 = 7.0;
    const C: [f64; 9] = [
        1.0,
        676.520_368_121_885_1,
        -1_259.139_216_722_402_8,
        771.323_428_777_653_1,
        -176.615_029_162_140_6,
        12.507_343_278_686_905,
        -0.138_571_095_265_720_12,
        9.984_369_578_019_572e-6,
        1.505_632_735_149_311_6e-7,
    ];
    if z < 0.5 {
        // Reflection: Γ(z)Γ(1−z) = π / sin(πz). (Unused for a, b > 0.)
        (std::f64::consts::PI / (std::f64::consts::PI * z).sin()).ln() - ln_gamma(1.0 - z)
    } else {
        let z = z - 1.0;
        let mut x = C[0];
        for (i, c) in C.iter().enumerate().skip(1) {
            x += c / (z + i as f64);
        }
        let t = z + G + 0.5;
        0.5 * (2.0 * std::f64::consts::PI).ln() + (z + 0.5) * t.ln() - t + x.ln()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ClassMeasurement;

    fn chal() -> ChallengeDefinition {
        let mut d: ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../challenges/chl_4b4316516128000f129cff9b3ced8b51.json"
        ))
        .unwrap();
        d.coverage = Some(spec());
        d
    }

    fn spec() -> CoverageSpec {
        CoverageSpec {
            version: COVERAGE_VERSION.into(),
            succinct: None,
            statement_spec: "NearSpecV3.challengeSpecChunkTop".into(),
            soundness_lift: "NearSpecV3.sound_lift".into(),
            tiers: vec![
                CoverageTier {
                    id: "D0".into(),
                    rank: 0,
                    params: "NearSpecV3.challengeParamsChunk .d0".into(),
                    classes: vec!["d0-quiet".into()],
                },
                CoverageTier {
                    id: "D1".into(),
                    rank: 1,
                    params: "NearSpecV3.challengeParamsChunk .d1".into(),
                    classes: vec!["d0-quiet".into(), "d0-transfers".into()],
                },
            ],
        }
    }

    #[test]
    fn validates() {
        let c = chal();
        c.coverage.as_ref().unwrap().validate(&c).unwrap();
        let mut s = spec();
        s.tiers[1].classes = vec!["d0-transfers".into()];
        assert!(s.validate(&c).unwrap_err().contains("omits class"));
        let mut s = spec();
        s.tiers[1].rank = 0;
        assert!(s
            .validate(&c)
            .unwrap_err()
            .contains("duplicate coverage tier rank"));
        let mut s = spec();
        s.tiers[0].classes.push("nope".into());
        assert!(s.validate(&c).is_err());
        let mut s = spec();
        s.version = "coverage-v2".into();
        assert!(s.validate(&c).is_err());
    }

    #[test]
    fn absent_coverage_keeps_the_challenge_id() {
        let raw = include_str!("../../../challenges/chl_4b4316516128000f129cff9b3ced8b51.json");
        let d: ChallengeDefinition = serde_json::from_str(raw).unwrap();
        assert!(d.coverage.is_none());
        assert_eq!(d.id().unwrap(), "chl_4b4316516128000f129cff9b3ced8b51");
        let mut with = d.clone();
        with.coverage = Some(spec());
        assert_ne!(with.id().unwrap(), d.id().unwrap());
        let back: ChallengeDefinition =
            serde_json::from_str(&serde_json::to_string(&with).unwrap()).unwrap();
        assert_eq!(back, with);
    }

    /// v1.7: `workload_suite.weight_source` is serialized only when present
    /// (signed ids unchanged), carries `ref` under that wire name, and is
    /// validated with the coverage section.
    #[test]
    fn weight_source_is_additive_and_validated() {
        use crate::challenge::{WeightSource, WeightSourceStatus};
        let raw = include_str!("../../../challenges/chl_4b4316516128000f129cff9b3ced8b51.json");
        let d: ChallengeDefinition = serde_json::from_str(raw).unwrap();
        assert!(d.workload_suite.weight_source.is_none());
        assert!(!serde_json::to_string(&d).unwrap().contains("weight_source"));
        assert_eq!(d.id().unwrap(), "chl_4b4316516128000f129cff9b3ced8b51");
        let mut c = chal();
        c.workload_suite.weight_source = Some(WeightSource {
            status: WeightSourceStatus::Assumed,
            note: "documented assumption".into(),
            reference: Some("spec/challenge-inputs/near-chunk-v3-weights.json".into()),
        });
        c.check_coverage().unwrap();
        let j = serde_json::to_value(&c).unwrap();
        assert_eq!(j["workload_suite"]["weight_source"]["status"], "ASSUMED");
        assert_eq!(
            j["workload_suite"]["weight_source"]["ref"],
            "spec/challenge-inputs/near-chunk-v3-weights.json"
        );
        let back: ChallengeDefinition = serde_json::from_value(j).unwrap();
        assert_eq!(back, c);
        assert_ne!(back.id().unwrap(), chal().id().unwrap());
        fn ws(c: &mut ChallengeDefinition) -> &mut WeightSource {
            c.workload_suite.weight_source.as_mut().unwrap()
        }
        ws(&mut c).status = WeightSourceStatus::Measured;
        c.check_coverage().unwrap();
        ws(&mut c).reference = None;
        assert!(c.check_coverage().unwrap_err().contains("MEASURED"));
        ws(&mut c).status = WeightSourceStatus::Assumed;
        c.check_coverage().unwrap();
        ws(&mut c).note = " ".into();
        assert!(c.check_coverage().is_err());
        // unknown status / fields are refused
        assert!(
            serde_json::from_str::<WeightSource>(r#"{"status":"GUESSED","note":"x"}"#).is_err()
        );
        assert!(serde_json::from_str::<WeightSource>(
            r#"{"status":"ASSUMED","note":"x","by":"y"}"#
        )
        .is_err());
    }

    /// Tiers are data: a tier below D0 (`D0a`, D0a ⊂ D0, so rank(D0a) <
    /// rank(D0)) needs no code change; ids and ranks come from the challenge.
    #[test]
    fn a_sub_d0_tier_is_ranked_by_the_challenge() {
        let mut c = chal();
        let mut s = spec();
        for t in &mut s.tiers {
            t.rank += 1;
        }
        s.tiers.insert(
            0,
            CoverageTier {
                id: "D0a".into(),
                rank: 0,
                params: "NearSpecV3.challengeParamsChunk .d0a".into(),
                classes: vec!["d0-quiet".into()],
            },
        );
        s.validate(&c).unwrap();
        c.coverage = Some(s.clone());
        let m = crate::CandidateManifest::parse(
            &include_str!("../../../examples/reexec-v3-d0/candidate.toml").replace(
                "verify_route = \"native-lean\"",
                "verify_route = \"native-lean\"\ndeclared_tier = \"D0a\"",
            ),
        )
        .unwrap();
        let t = c.declared_tier(&m).unwrap().unwrap();
        assert_eq!((t.id.as_str(), t.rank), ("D0a", 0));
        assert!(t.rank < s.tier("D0").unwrap().rank);
        // a D0a tier listing a class D0 does not would break inclusion
        s.tiers[0].classes.push("d0-missing".into());
        assert!(s.validate(&c).unwrap_err().contains("omits class"));
    }

    #[test]
    fn declared_tier_required_iff_coverage() {
        let raw = include_str!("../../../examples/reexec-v3-d0/candidate.toml");
        let m = crate::CandidateManifest::parse(raw).unwrap();
        let c = chal();
        assert!(c.declared_tier(&m).unwrap_err().contains("required"));
        let with = crate::CandidateManifest::parse(&raw.replace(
            "verify_route = \"native-lean\"",
            "verify_route = \"native-lean\"\ndeclared_tier = \"D1\"",
        ))
        .unwrap();
        assert_eq!(with.entry.declared_tier.as_deref(), Some("D1"));
        assert_eq!(c.declared_tier(&with).unwrap().unwrap().rank, 1);
        let mut unknown = with.clone();
        unknown.entry.declared_tier = Some("D9".into());
        assert!(c.declared_tier(&unknown).is_err());
        let mut plain = c.clone();
        plain.coverage = None;
        assert!(plain.declared_tier(&m).unwrap().is_none());
        assert!(plain
            .declared_tier(&with)
            .unwrap_err()
            .contains("only valid"));
        // the manifest field is syntax-checked and serialized only when present
        assert!(crate::CandidateManifest::parse(&raw.replace(
            "verify_route = \"native-lean\"",
            "verify_route = \"native-lean\"\ndeclared_tier = \"D 1\""
        ))
        .is_err());
        assert!(!serde_json::to_string(&m).unwrap().contains("declared_tier"));
    }

    #[test]
    fn renormalizes_exactly() {
        assert_eq!(
            renormalize_ppm(&[200_000, 500_000]).unwrap(),
            vec![285_714, 714_286]
        );
        assert_eq!(
            renormalize_ppm(&[1, 1, 1]).unwrap().iter().sum::<u32>(),
            1_000_000
        );
        assert_eq!(renormalize_ppm(&[1_000_000]).unwrap(), vec![1_000_000]);
        assert!(renormalize_ppm(&[0, 0]).is_none());
    }

    #[test]
    fn share_is_weighted_over_classes_with_cases() {
        let c = chal();
        let w: BTreeMap<&str, u32> = c
            .workload_suite
            .classes
            .iter()
            .map(|x| (x.id.as_str(), x.weight_ppm))
            .collect();
        let mut s = CoverageSection::default();
        s.record(None, true, false); // fixture: not a class
        s.record(Some("d0-quiet"), true, false);
        s.record(Some("d0-transfers"), false, true);
        s.record(Some("d0-transfers"), true, false);
        s.finish(&c);
        let (wq, wt) = (w["d0-quiet"] as u128, w["d0-transfers"] as u128);
        let want = (wq * 1_000_000 + wt * 500_000) / (wq + wt);
        assert_eq!(s.share_ppm as u128, want);
        assert_eq!(s.per_class[FIXTURES_KEY].cases, 1);
        assert_eq!(s.per_class["d0-transfers"].abstained, 1);
    }

    // ---- held-out covert channel (CONTRACTS §11) ----------------------------

    #[test]
    fn heldout_is_published_aggregate_only() {
        let mut heldout = CoverageSection::default();
        heldout.record(Some("d0-quiet"), true, false);
        heldout.record(Some("d0-quiet"), true, false);
        heldout.record(Some("d0-transfers"), false, true);
        heldout.record(Some("d1-transfers"), true, false);
        heldout.share_ppm = 750_000;
        let report = CoverageReport {
            tier: "D1".into(),
            conformance: CoverageSection::default(),
            heldout: Some(heldout),
        };
        let pubd = CoveragePublic::of_report(&report);
        let h = pubd.heldout.clone().unwrap();
        assert_eq!((h.cases, h.proven, h.abstained), (4, 3, 1));
        assert_eq!(h.share_ppm, 750_000);
        // The wire form of the published held-out section carries no
        // per-class breakdown at all.
        let j = serde_json::to_value(&pubd).unwrap();
        let hj = &j["heldout"];
        assert_eq!(hj.as_object().unwrap().len(), 4);
        assert!(hj.get("per_class").is_none());
        assert!(
            serde_json::from_str::<CoveragePublic>(&serde_json::to_string(&pubd).unwrap()).is_ok()
        );
        // Conformance passes through unchanged (public fixtures and classes).
        let mut conf = CoverageSection::default();
        conf.record(Some("d0-quiet"), true, false);
        let report = CoverageReport {
            tier: "D1".into(),
            conformance: conf,
            heldout: None,
        };
        let pubd = CoveragePublic::of_report(&report);
        assert_eq!(pubd.conformance.per_class.len(), 1);
        assert!(pubd.heldout.is_none());
    }

    // ---- succinct badge (BENCHMARK_SPEC §17) --------------------------------

    fn succinct() -> SuccinctSpec {
        SuccinctSpec {
            max_proof_bytes: 2 * 1024 * 1024,
            max_verify_ns: 50_000_000,
            exponent_bound_ppm: 0,
            ucb_bound_ppm: 0,
        }
    }

    fn class_with_gas(id: &str, gas: u64, bytes: u64, verify_ns: u64) -> ClassMeasurement {
        ClassMeasurement {
            class_id: id.into(),
            weight_ppm: 100_000,
            runs_ns: vec![1; 5],
            median_ns: 1,
            mad_ns: 0,
            cold_ns: None,
            baseline_ns: 1,
            verify_median_ns: verify_ns,
            proof_bytes_max: bytes,
            peak_rss_bytes: 0,
            verify_runs_ns: vec![verify_ns; 5],
            proof_bytes_runs: vec![bytes; 5],
            abstained: false,
            ref_runs_ns: vec![],
            ref_verify_runs_ns: vec![],
            ref_proof_bytes_runs: vec![],
            gas_runs: vec![gas; 5],
        }
    }

    /// Student-t 95% quantiles at the usual dof table values.
    #[test]
    fn student_t_quantiles_match_the_table() {
        let want = [(1.0, 6.3138), (2.0, 2.9200), (10.0, 1.8125), (30.0, 1.6973)];
        for (dof, t) in want {
            assert!(
                (student_t_95_upper(dof) - t).abs() < 2e-3,
                "dof {dof}: {} vs {t}",
                student_t_95_upper(dof)
            );
        }
        // Normal limit as dof grows.
        assert!((student_t_95_upper(10_000.0) - 1.6449).abs() < 2e-3);
    }

    #[test]
    fn succinct_field_is_additive() {
        let d = chal(); // coverage = Some(spec()), succinct = None
        assert!(d.coverage.as_ref().unwrap().succinct.is_none());
        let bare_id = d.id().unwrap();
        let mut with = d.clone();
        with.coverage.as_mut().unwrap().succinct = Some(succinct());
        assert_ne!(with.id().unwrap(), bare_id);
        let j = serde_json::to_string(&with).unwrap();
        assert!(j.contains("\"succinct\""));
        // A challenge without the badge must not grow the wire form.
        assert!(!serde_json::to_string(&d).unwrap().contains("succinct"));
        let back: ChallengeDefinition = serde_json::from_str(&j).unwrap();
        assert_eq!(back.coverage.unwrap().succinct, Some(succinct()));
    }

    #[test]
    fn badge_granted_on_flat_proofs_with_gas() {
        let mut c = chal();
        c.coverage.as_mut().unwrap().succinct = Some(succinct());
        // Proof bytes and verify time constant while gas grows 4 decades.
        let classes = [
            class_with_gas("small", 1_000, 100_000, 1_000_000),
            class_with_gas("mid", 10_000_000, 100_000, 1_000_000),
            class_with_gas("big", 100_000_000_000, 100_000, 1_000_000),
        ];
        let b = c
            .coverage
            .as_ref()
            .unwrap()
            .evaluate_succinct(&classes)
            .unwrap();
        assert!(b.granted, "{:?}", b.denied);
        assert_eq!(b.max_proof_bytes, 100_000);
        assert_eq!(b.max_verify_ns, 1_000_000);
        let exp = b.bytes_exponent_ppm.unwrap().unsigned_abs();
        assert!(exp <= 100_000, "bytes exponent {exp} ppm");
        assert!(b.bytes_ucb_ppm.unwrap().unsigned_abs() <= 250_000);
    }

    #[test]
    fn badge_denied_when_proofs_grow_with_gas() {
        let mut c = chal();
        c.coverage.as_mut().unwrap().succinct = Some(succinct());
        // bytes ∝ gas^0.5: exponent ≈ 500,000 ppm, way over the bound.
        let classes = [
            class_with_gas("small", 1_000, 10_000, 1_000_000),
            class_with_gas("mid", 10_000_000, 10_000 * 3162, 1_000_000),
            class_with_gas("big", 1_000_000_000_000, 10_000 * 1_000_000, 1_000_000),
        ];
        let b = c
            .coverage
            .as_ref()
            .unwrap()
            .evaluate_succinct(&classes)
            .unwrap();
        assert!(!b.granted);
        assert!(b.bytes_exponent_ppm.unwrap() > 250_000);
        assert!(b.denied.iter().any(|d| d.contains("bytes")));
    }

    #[test]
    fn badge_denied_on_thresholds() {
        let mut c = chal();
        c.coverage.as_mut().unwrap().succinct = Some(succinct());
        let classes = [class_with_gas("big", 1, u32::MAX as u64, 60_000_000)];
        let b = c
            .coverage
            .as_ref()
            .unwrap()
            .evaluate_succinct(&classes)
            .unwrap();
        assert!(!b.granted);
        assert!(b.denied.iter().any(|d| d.contains("proof")));
        assert!(b.denied.iter().any(|d| d.contains("verify")));
    }

    /// Fail-closed: without a gas axis there is no growth test.
    #[test]
    fn badge_denied_without_gas_data() {
        let mut c = chal();
        c.coverage.as_mut().unwrap().succinct = Some(succinct());
        let classes = [class_with_gas("flat", 0, 100, 1_000)];
        let b = c
            .coverage
            .as_ref()
            .unwrap()
            .evaluate_succinct(&classes)
            .unwrap();
        assert!(!b.granted);
        assert!(b.bytes_exponent_ppm.is_none());
        assert!(b.denied.iter().any(|d| d.contains("slope test")));
    }

    #[test]
    fn badge_ignores_abstained_classes() {
        let mut c = chal();
        c.coverage.as_mut().unwrap().succinct = Some(succinct());
        let mut big = class_with_gas("abstained", 1, u64::MAX, u64::MAX);
        big.abstained = true;
        let classes = [big, class_with_gas("ok", 1_000, 100, 1_000)];
        let b = c
            .coverage
            .as_ref()
            .unwrap()
            .evaluate_succinct(&classes)
            .unwrap();
        assert_eq!(b.max_proof_bytes, 100);
    }
}
