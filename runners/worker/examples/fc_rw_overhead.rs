//! `fc_rw_overhead` — the Firecracker sandbox overhead of a read-write dir
//! of a given size, per run, the way the formal checker's per-module runs
//! pay it: (a) one microVM per run (`/bin/true` with the dir as rw bind:
//! seed image + guest copy + write-back of the whole dir), (b) one steps-mode
//! microVM for N runs (overlay; only changes written back).
//!
//! ```text
//! cargo run --release -p arena-worker --example fc_rw_overhead -- \
//!   FC_DEPS WORK_DIR RW_DIR CPU [N_SINGLE] [N_STEPS]
//! ```
//! `RW_DIR` is only read: it is copied into WORK_DIR first. The
//! process pins itself to CPU, CPU+1 once the sandbox is set up.
use arena_sandbox::{Mount, Sandbox, SandboxSpec, StepSpec, StepsOptions};
use std::path::PathBuf;
use std::time::{Duration, Instant};

fn copy_links(from: &std::path::Path, to: &std::path::Path) {
    let st = std::process::Command::new("cp")
        .arg("-a")
        .arg(from)
        .arg(to)
        .status()
        .unwrap();
    assert!(st.success());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let deps = PathBuf::from(&a[1]);
    let work = PathBuf::from(&a[2]);
    let src = PathBuf::from(&a[3]);
    let cpu: u32 = a[4].parse().unwrap();
    let n_single: usize = a.get(5).map(|s| s.parse().unwrap()).unwrap_or(3);
    let n_steps: usize = a.get(6).map(|s| s.parse().unwrap()).unwrap_or(64);
    std::fs::create_dir_all(&work).unwrap();
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &work.join("fc")).unwrap();
    let sb = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    // pin this process (staging, image builds) next to its VM's CPU
    unsafe {
        let mut set: libc::cpu_set_t = std::mem::zeroed();
        libc::CPU_SET(cpu as usize, &mut set);
        libc::CPU_SET(cpu as usize + 1, &mut set);
        assert_eq!(
            libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set),
            0
        );
    }
    let rw = work.join("rw");
    let _ = std::fs::remove_dir_all(&rw);
    copy_links(&src, &rw);
    let du = std::process::Command::new("du")
        .args(["-sb", "--apparent-size"])
        .arg(&rw)
        .output()
        .unwrap();
    let bytes = String::from_utf8_lossy(&du.stdout)
        .split_whitespace()
        .next()
        .unwrap_or("0")
        .to_string();
    let mut base = SandboxSpec::new(vec!["/bin/true".into()]);
    base.cwd = "/scratch".into();
    base.rw_binds = vec![Mount {
        host: rw.clone(),
        guest: "/arena/out".into(),
    }];
    base.allow_mount_symlinks = true;
    base.cpu_set = Some(vec![cpu]);
    base.mem_bytes = 4 << 30;
    base.pids = 256;
    base.rw_scratch_mb = 8192;
    base.max_output_bytes = 8 << 30;
    base.wall_timeout = Duration::from_secs(600);
    base.syscall_policy = arena_sandbox::SyscallPolicy::Tooling;
    println!("rw tree: {bytes} bytes");
    for i in 0..n_single {
        let t = Instant::now();
        let o = sb.run(&base).unwrap();
        println!(
            "single run {i}: {:.2} s (exit {:?}, output error {:?}, violations {:?})",
            t.elapsed().as_secs_f64(),
            o.exit,
            o.output_error,
            o.diagnostics.output_violations
        );
    }
    let mut b = base.clone();
    b.steps = StepsOptions {
        deadline: Some(Duration::from_secs(600)),
        start_deadline: None,
        full_capture_last: true,
    };
    let steps: Vec<StepSpec> = (0..n_steps)
        .map(|_| StepSpec {
            argv: vec!["/bin/true".into()],
            ro_files: vec![],
            collect: vec![],
            out_dir: None,
            wall_timeout: Duration::from_secs(60),
        })
        .collect();
    let t = Instant::now();
    let outs = sb.run_steps(&b, &steps).unwrap();
    let el = t.elapsed().as_secs_f64();
    assert_eq!(outs.len(), n_steps);
    assert!(outs.iter().all(|o| o.output_error.is_none()));
    println!(
        "steps: {n_steps} runs in one VM: {el:.2} s total, {:.3} s per run",
        el / n_steps as f64
    );
}
