//! `formal_fc` — run the formal checker on one candidate exactly as the
//! worker's FORMAL_CHECK does on its sandbox (`SandboxRunner` over the
//! backend, the lean-checker image as the root of every Firecracker run,
//! `Limits::from_env()` + `ARENA_FORMAL_MEM_BYTES`), for local validation of
//! the production formal path. Writes the `FormalCheckReport` JSON.
//!
//! ```text
//! cargo run --release -p arena-worker --example formal_fc -- \
//!   --backend firecracker --fc-deps DIR --lean-images DIR [--cpus 10] [--driver-cpus 10-13,26-29] \
//!   --formal F --certificate C \
//!   ( --challenge chl.json --challenge-config cfg.json --trusted-store STORE --public-digest HEX
//!       [--verifier-digest HEX] [--native-model DECL@MODULE --candidate-native-binary FILE]
//!   | --corpus-case DIR )   # runners/formal-checker/tests/corpus/<case> with the stand-in package
//!   [--work DIR] [--cache DIR] --out report.json
//! ```
//! `--backend bwrap` (needs `ARENA_DEV_UNSAFE=1`) runs the same check on
//! bwrap-dev with host tools (one sandbox run per module: the reference for
//! comparisons). `--cpus` pins every microVM (one vCPU per listed CPU);
//! `--driver-cpus` pins this process after the sandbox is set up.
use arena_formal_checker::native::{NativeLeanRoute, VerifierRoute};
use arena_formal_checker::*;
use arena_types::ObligationId;
use std::path::{Path, PathBuf};
use std::sync::Arc;

fn parse_cpus(s: &str) -> Vec<u32> {
    let mut v = Vec::new();
    for part in s.split(',') {
        match part.split_once('-') {
            Some((a, b)) => v.extend(a.parse::<u32>().unwrap()..=b.parse::<u32>().unwrap()),
            None => v.push(part.parse().unwrap()),
        }
    }
    v
}

fn pin_self(cpus: &[u32]) {
    unsafe {
        let mut set: libc::cpu_set_t = std::mem::zeroed();
        for c in cpus {
            libc::CPU_SET(*c as usize, &mut set);
        }
        assert_eq!(
            libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set),
            0,
            "sched_setaffinity"
        );
    }
}

/// Pins every microVM of the wrapped Firecracker sandbox to `cpus`.
struct Pinned {
    inner: arena_firecracker::FirecrackerSandbox,
    cpus: Option<Vec<u32>>,
    /// `--no-batch`: report no shared-instance steps, so the checker issues
    /// one microVM run per module (the pre-batching path).
    no_batch: bool,
}

impl arena_sandbox::Sandbox for Pinned {
    fn name(&self) -> &str {
        self.inner.name()
    }
    fn tier_cap(&self) -> Option<arena_types::challenge::Tier> {
        self.inner.tier_cap()
    }
    fn layout(&self) -> arena_sandbox::GuestLayout {
        self.inner.layout()
    }
    fn steps_share_instance(&self) -> bool {
        !self.no_batch && self.inner.steps_share_instance()
    }
    fn run(
        &self,
        spec: &arena_sandbox::SandboxSpec,
    ) -> Result<arena_sandbox::SandboxOutcome, arena_sandbox::InfraError> {
        let mut s = spec.clone();
        if self.cpus.is_some() {
            s.cpu_set = self.cpus.clone();
        }
        self.inner.run(&s)
    }
    fn run_steps(
        &self,
        base: &arena_sandbox::SandboxSpec,
        steps: &[arena_sandbox::StepSpec],
    ) -> Result<Vec<arena_sandbox::SandboxOutcome>, arena_sandbox::InfraError> {
        let mut s = base.clone();
        if self.cpus.is_some() {
            s.cpu_set = self.cpus.clone();
        }
        self.inner.run_steps(&s, steps)
    }
}

fn main() -> anyhow::Result<()> {
    let all: Vec<String> = std::env::args().collect();
    if all.get(1).map(String::as_str) == Some(arena_formal_checker::HELPER_ARG) {
        std::process::exit(arena_sandbox::helper::helper_main(&all[2..]));
    }
    let mut args = std::env::args().skip(1);
    let (mut backend, mut fc_deps, mut lean_images, mut cpus, mut driver_cpus) =
        (String::from("firecracker"), None, None, None, None);
    let (mut formal, mut cert, mut out, mut corpus) = (None, None, None, None);
    let (mut chal, mut chal_cfg, mut store, mut pub_d, mut ver_d) = (None, None, None, None, None);
    let (mut native_model, mut cand_bin): (Option<String>, Option<PathBuf>) = (None, None);
    let mut work = std::env::temp_dir().join(format!("formal-fc-{}", std::process::id()));
    let mut cache = None;
    let mut no_batch = false;
    let mut fc_work: Option<PathBuf> = None;
    let mut cand_digest: Option<arena_types::Digest> = None;
    while let Some(a) = args.next() {
        let mut v = || {
            args.next()
                .ok_or_else(|| anyhow::anyhow!("missing value for {a}"))
        };
        match a.as_str() {
            "--backend" => backend = v()?,
            "--no-batch" => no_batch = true,
            "--fc-work" => fc_work = Some(PathBuf::from(v()?)),
            "--fc-deps" => fc_deps = Some(PathBuf::from(v()?)),
            "--lean-images" => lean_images = Some(PathBuf::from(v()?)),
            "--cpus" => cpus = Some(parse_cpus(&v()?)),
            "--driver-cpus" => driver_cpus = Some(parse_cpus(&v()?)),
            "--formal" => formal = Some(PathBuf::from(v()?)),
            "--certificate" => cert = Some(v()?),
            "--out" => out = Some(PathBuf::from(v()?)),
            "--work" => work = PathBuf::from(v()?),
            "--cache" => cache = Some(PathBuf::from(v()?)),
            "--corpus-case" => corpus = Some(PathBuf::from(v()?)),
            "--challenge" => chal = Some(PathBuf::from(v()?)),
            "--challenge-config" => chal_cfg = Some(PathBuf::from(v()?)),
            "--trusted-store" => store = Some(PathBuf::from(v()?)),
            "--public-digest" => pub_d = Some(v()?),
            "--verifier-digest" => ver_d = Some(v()?),
            "--native-model" => native_model = Some(v()?),
            "--candidate-native-binary" => cand_bin = Some(PathBuf::from(v()?)),
            "--candidate-native-digest" => {
                cand_digest = Some(
                    arena_types::Digest::try_from(format!("sha256:{}", v()?))
                        .map_err(|e| anyhow::anyhow!(e))?,
                )
            }
            _ => anyhow::bail!("unknown argument {a}"),
        }
    }
    let out = out.ok_or_else(|| anyhow::anyhow!("--out required"))?;
    std::fs::create_dir_all(&work)?;
    let cache = cache.unwrap_or_else(|| work.join("ref-cache"));

    // Sandbox + tools, as the worker (`stages/formal.rs::tools_for`).
    let (sandbox, tools, rootfs): (Arc<dyn arena_sandbox::Sandbox>, toolchain::ToolPaths, _) =
        match backend.as_str() {
            "firecracker" => {
                let deps = fc_deps.ok_or_else(|| anyhow::anyhow!("--fc-deps required"))?;
                let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(
                    &deps,
                    &fc_work.clone().unwrap_or_else(|| work.join("firecracker")),
                )?;
                let sb = arena_firecracker::FirecrackerSandbox::new(cfg)?;
                eprintln!("formal_fc: firecracker rootfs {}", sb.rootfs_digest());
                let images =
                    lean_images.ok_or_else(|| anyhow::anyhow!("--lean-images required"))?;
                let mut metas: Vec<(std::time::SystemTime, PathBuf)> = std::fs::read_dir(&images)?
                    .flatten()
                    .map(|e| e.path())
                    .filter(|p| p.extension().is_some_and(|x| x == "json"))
                    .filter_map(|p| Some((p.metadata().ok()?.modified().ok()?, p)))
                    .collect();
                metas.sort();
                let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(
                    &metas
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("no lean-checker image"))?
                        .1,
                )?)?;
                let digest: arena_types::Digest = meta["digest"]
                    .as_str()
                    .unwrap_or("")
                    .to_string()
                    .try_into()
                    .map_err(|e: String| anyhow::anyhow!(e))?;
                let dir = images.join(digest.hex());
                eprintln!("formal_fc: lean-checker image {digest}");
                let tools = toolchain::ToolPaths {
                    lean_sysroot: dir.join("arena/tc"),
                    lean4export: dir.join("arena/tools/lean4export"),
                    nanoda: Some(dir.join("arena/tools/nanoda_bin")).filter(|p| p.is_file()),
                    lean4lean: Some(dir.join("arena/tools/lean4lean")).filter(|p| p.is_file()),
                    arena_audit: dir.join("arena/tools/arena-audit"),
                };
                let sb: Arc<dyn arena_sandbox::Sandbox> = Arc::new(Pinned {
                    inner: sb,
                    cpus,
                    no_batch,
                });
                (
                    sb,
                    tools,
                    arena_sandbox::Rootfs::Image { path: dir, digest },
                )
            }
            "bwrap" => {
                let helper = arena_sandbox::HelperCommand {
                    exe: std::env::current_exe()?,
                    prefix_args: vec![arena_formal_checker::HELPER_ARG.into()],
                };
                let sb = arena_sandbox::BwrapDev::new(arena_sandbox::BwrapConfig::new(
                    helper,
                    work.join("sandbox"),
                ))?;
                (
                    Arc::new(sb),
                    toolchain::ToolPaths::discover()?,
                    arena_sandbox::Rootfs::BackendDefault,
                )
            }
            b => anyhow::bail!("unknown backend {b}"),
        };
    if let Some(c) = &driver_cpus {
        pin_self(c);
    }
    let runner = SandboxRunner::new(sandbox, work.join("fc-sandbox"))?.with_rootfs(rootfs);
    let checker = FormalChecker::new(tools, Box::new(runner));
    let mut limits = Limits::from_env();
    limits.mem_bytes = std::env::var("ARENA_FORMAL_MEM_BYTES").ok().and_then(|v| {
        let v = v.trim();
        let (n, m) = match v.strip_suffix('G') {
            Some(n) => (n, 1u64 << 30),
            None => (v, 1),
        };
        n.parse::<u64>().ok().map(|n| n * m)
    });

    let expected: TemplateExpected;
    let mut policy = Policy::default();
    let mut trusted = Vec::new();
    let mut trusted_tree = None;
    let mut route = VerifierRoute::Standard;
    let formal_dir;
    let certificate;
    if let Some(case) = &corpus {
        // runners/formal-checker/tests/corpus.rs semantics
        let fc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../formal-checker");
        let expect: serde_json::Value =
            serde_json::from_slice(&std::fs::read(case.join("expect.json"))?)?;
        expected =
            serde_json::from_slice(&std::fs::read(fc.join("tests/fixtures/expected.json"))?)?;
        trusted.push(TrustedPackage {
            name: "arena-standin".into(),
            src_root: fc.join("tests/fixtures/standin"),
            include: None,
        });
        policy.allowed_requires = vec!["arena-standin".into()];
        if expect.get("conjuncts").and_then(|v| v.as_bool()) == Some(true) {
            policy.conjunct_gates = Some(vec![
                ObligationId::FormalSemanticSoundness,
                ObligationId::FormalSemanticCompleteness,
                ObligationId::FormalCryptoSoundness,
                ObligationId::FormalImplConnection,
            ]);
        }
        if let Some(t) = expect.get("module_timeout_s").and_then(|v| v.as_u64()) {
            limits.module_timeout = std::time::Duration::from_secs(t);
        }
        if expect.get("route").and_then(|v| v.as_str()) == Some("candidate-native") {
            route = VerifierRoute::CandidateNative;
        }
        formal_dir = case.join("formal");
        certificate = "Candidate.certificate".to_string();
    } else {
        if let Some(nm) = &native_model {
            let (d, m) = nm
                .split_once('@')
                .ok_or_else(|| anyhow::anyhow!("--native-model DECL@MODULE"))?;
            let mut r = NativeLeanRoute::new(d, m);
            if let Some(b) = &cand_bin {
                r.candidate_binary_digest = Some(digest::sha256_file(b)?);
            }
            if let Some(d) = &cand_digest {
                r.candidate_binary_digest = Some(d.clone());
            }
            route = VerifierRoute::NativeLean(r);
        }
        let cfg = ChallengeFormalConfig::load(
            &chal_cfg.ok_or_else(|| anyhow::anyhow!("--challenge-config required"))?,
        )?;
        let def: arena_types::ChallengeDefinition = serde_json::from_slice(&std::fs::read(
            chal.ok_or_else(|| anyhow::anyhow!("--challenge required"))?,
        )?)?;
        let pin = def.semantic_scope.formal_spec.tree_digest.clone();
        let root = work.join("trusted-tree");
        let _ = std::fs::remove_dir_all(&root);
        arena_types::trusted_tree::materialize(
            &store.ok_or_else(|| anyhow::anyhow!("--trusted-store required"))?,
            &pin,
            &root,
        )
        .map_err(|e| anyhow::anyhow!("pinned trusted tree: {e}"))?;
        trusted_tree = Some(pin);
        let inp = ExpectedInputs::from_definition(
            &def,
            pub_d.ok_or_else(|| anyhow::anyhow!("--public-digest required"))?,
            match (&route, ver_d) {
                (VerifierRoute::NativeLean(_), _) => String::new(),
                (_, d) => d.ok_or_else(|| anyhow::anyhow!("--verifier-digest required"))?,
            },
        )?;
        trusted.extend(cfg.trusted_packages(&root));
        policy
            .reserved_prefixes
            .extend(cfg.reserved_prefixes.iter().cloned());
        policy.axiom_allowlist = def.toolchain_policy.axiom_allowlist.clone();
        policy.gates.retain(|g| {
            def.required_obligations.contains(&g.gate) || g.gate == ObligationId::AxiomAudit
        });
        expected = if matches!(route, VerifierRoute::NativeLean(_)) {
            cfg.expected_native_lean(&root, &inp)?
        } else {
            cfg.expected(&root, &inp)?
        };
        formal_dir = formal.ok_or_else(|| anyhow::anyhow!("--formal required"))?;
        certificate = cert.ok_or_else(|| anyhow::anyhow!("--certificate required"))?;
    }
    let req = CheckRequest {
        formal_dir,
        certificate,
        trusted,
        expected: &expected,
        challenge_digest: None,
        trusted_tree,
        policy,
        limits,
        work_dir: work.join("formal-work"),
        cache_dir: cache,
        route,
    };
    let t = std::time::Instant::now();
    let report = checker.check(&req);
    eprintln!("formal_fc: check took {:.1} s", t.elapsed().as_secs_f64());
    std::fs::write(&out, serde_json::to_string_pretty(&report)?)?;
    for g in &report.gates {
        eprintln!("  {:?} {:?} {:?}", g.gate, g.status, g.reason_codes);
    }
    Ok(())
}
