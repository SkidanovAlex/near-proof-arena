use anyhow::{bail, ensure, Context, Result};
use compression_methods::{COMPRESS_GUEST_ELF, COMPRESS_GUEST_ID};
use compression_verifier::{air::Air, journal, verifier::verify};
use risc0_zkvm::{sha::Digest, Executor, ExecutorEnv, ExternalProver, Prover, ProverOpts, Receipt};
use serde_json::json;
use sha2::{Digest as _, Sha256};
use std::{fs, path::Path, time::Instant};

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    ensure!(args.len() == 7, "usage: compression-host native|execute|reject|succinct|verify AIR PUBLIC CLAIM PROOF RECEIPT");
    // Never let development mode silently replace a real compression proof.
    ensure!(std::env::var("RISC0_DEV_MODE").unwrap_or_default().is_empty()
        || std::env::var("RISC0_DEV_MODE").unwrap() == "0", "disable RISC0_DEV_MODE");
    let air_bytes = fs::read(&args[2])?;
    let public = fs::read(&args[3])?;
    let claim = fs::read(&args[4])?;
    let expected = journal(&air_bytes, &public, &claim);
    let image = Digest::from(COMPRESS_GUEST_ID).to_string();
    if args[1] == "verify" {
        let bytes = fs::read(&args[6])?;
        let receipt: Receipt = bincode::deserialize(&bytes)?;
        let started = Instant::now();
        check_receipt(&receipt, &expected)?;
        let verify_seconds = started.elapsed().as_secs_f64();
        negative_checks(&receipt, &expected)?;
        println!("{}", json!({"action":"verify", "image_id":image,
            "receipt_bytes":bytes.len(), "seal_bytes":receipt.inner.seal_size(),
            "journal_bytes":receipt.journal.bytes.len(), "verify_seconds":verify_seconds,
            "under_300000_bytes":bytes.len() < 300000, "outer_negative_checks":4,
            "receipt_sha256":hex::encode(Sha256::digest(&bytes)), "accepted":true}));
        return Ok(());
    }
    let proof = fs::read(&args[5])?;
    let air = Air::from_json(std::str::from_utf8(&air_bytes)?).map_err(anyhow::Error::msg)?;
    let started = Instant::now();
    let native = verify(&air, &public, &claim, &proof);
    if args[1] == "reject" {
        ensure!(native.is_err(), "negative fixture accepted natively");
    } else {
        native.map_err(anyhow::Error::msg)?;
    }
    let native_seconds = started.elapsed().as_secs_f64();
    let mut report = json!({"action":args[1], "image_id":image,
        "inner_proof_bytes":proof.len(), "inner_proof_sha256":hex::encode(Sha256::digest(&proof)),
        "journal_hex":hex::encode(&expected), "native_verify_seconds":native_seconds});
    if args[1] == "native" { println!("{report}"); return Ok(()); }
    let mut builder = ExecutorEnv::builder();
    let cycle_limit: u64 = std::env::var("COMPRESSION_MAX_CYCLES")
        .unwrap_or_else(|_| (256u64 * 1024 * 1024).to_string()).parse()?;
    ensure!(cycle_limit > 0, "cycle limit must be positive");
    builder.session_limit(Some(cycle_limit));
    report["cycle_limit"] = json!(cycle_limit);
    for data in [&air_bytes, &public, &claim, &proof] { builder.write_frame(data); }
    let env = builder.build()?;
    let server = std::env::var("RISC0_SERVER_PATH")
        .context("set RISC0_SERVER_PATH to the local RISC Zero 3.0.6 r0vm executable")?;
    let prover = ExternalProver::new("compression-local", server);
    let started = Instant::now();
    if args[1] == "reject" {
        let error = prover.execute(env, COMPRESS_GUEST_ELF).err()
            .context("negative fixture accepted inside guest")?;
        let message = format!("{error:#}");
        ensure!(message.contains("inner proof rejected"), "unexpected execution failure: {message}");
        report["guest_rejected"] = json!(true);
        report["error"] = json!(message);
        report["execute_seconds"] = json!(started.elapsed().as_secs_f64());
    } else if args[1] == "execute" {
        let session = prover.execute(env, COMPRESS_GUEST_ELF)?;
        ensure!(session.journal.bytes == expected, "journal mismatch");
        report["execute_seconds"] = json!(started.elapsed().as_secs_f64());
        report["user_cycles"] = json!(session.cycles());
        report["padded_cycles"] = json!(session.segments.iter().map(|s| 1u64 << s.po2).sum::<u64>());
        report["segments"] = json!(session.segments.len());
    } else if args[1] == "succinct" {
        ensure!(!Path::new(&args[6]).exists(), "receipt output already exists");
        let info = prover.prove_with_opts(env, COMPRESS_GUEST_ELF, &ProverOpts::succinct())?;
        report["prove_seconds"] = json!(started.elapsed().as_secs_f64());
        report["user_cycles"] = json!(info.stats.user_cycles);
        report["segments"] = json!(info.stats.segments);
        let receipt = info.receipt;
        let started = Instant::now();
        check_receipt(&receipt, &expected)?;
        report["verify_seconds"] = json!(started.elapsed().as_secs_f64());
        let bytes = bincode::serialize(&receipt)?;
        report["receipt_bytes"] = json!(bytes.len());
        report["seal_bytes"] = json!(receipt.inner.seal_size());
        report["journal_bytes"] = json!(receipt.journal.bytes.len());
        report["under_300000_bytes"] = json!(bytes.len() < 300000);
        report["receipt_sha256"] = json!(hex::encode(Sha256::digest(&bytes)));
        negative_checks(&receipt, &expected)?;
        report["outer_negative_checks"] = json!(4);
        fs::write(&args[6], &bytes).context("saving receipt")?;
    } else { bail!("unknown action"); }
    println!("{report}");
    Ok(())
}

fn check_receipt(receipt: &Receipt, expected: &[u8]) -> Result<()> {
    ensure!(matches!(receipt.inner, risc0_zkvm::InnerReceipt::Succinct(_)), "real succinct receipt required");
    receipt.verify(COMPRESS_GUEST_ID)?;
    ensure!(receipt.journal.bytes == expected, "wrong AIR, public tape or claim");
    Ok(())
}

fn negative_checks(receipt: &Receipt, expected: &[u8]) -> Result<()> {
    // Mutations target both the statement binding and the outer cryptographic seal.
    let mut bad = receipt.clone();
    bad.journal.bytes[0] ^= 1;
    ensure!(check_receipt(&bad, expected).is_err(), "mutated journal accepted");
    let mut wrong = expected.to_vec(); wrong[0] ^= 1;
    ensure!(check_receipt(receipt, &wrong).is_err(), "wrong statement accepted");
    let mut wrong_id = COMPRESS_GUEST_ID; wrong_id[0] ^= 1;
    ensure!(receipt.verify(wrong_id).is_err(), "wrong image accepted");
    let mut bad = receipt.clone();
    if let risc0_zkvm::InnerReceipt::Succinct(inner) = &mut bad.inner {
        inner.seal[0] ^= 1;
    } else { bail!("expected succinct receipt"); }
    ensure!(check_receipt(&bad, expected).is_err(), "mutated seal accepted");
    Ok(())
}
