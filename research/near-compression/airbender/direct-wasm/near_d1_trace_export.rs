//! Research-only export of the existing candidate's real 33-table D1 traces.
//! Uses native case_inputs_d1/renderers and checks all local/bus obligations.
//! No prover, padding alteration, table substitution or synthetic witness.
use npudr::{air::Air, cols::TraceCols, v3::{d1, prove as vp}};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::{BufWriter, Write}, path::PathBuf};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 || !matches!(args[4].as_str(), "--check-only" | "--dump") {
        return Err("usage: near-d1-trace-export CASE_DIR AIR_JSON OUTPUT_DIR --check-only|--dump".into());
    }
    let case=PathBuf::from(&args[1]); let output=PathBuf::from(&args[3]);
    let air_text=fs::read_to_string(&args[2])?;
    let air=Air::from_json(&air_text)?.with_aux_group(2);
    if air.tables.len()!=33 { return Err("expected canonical 33-table nearAirV3D1 export".into()); }
    let cb=fs::read(case.join("claim.bin"))?; let wb=fs::read(case.join("witness.bin"))?;
    let ci=d1::case_inputs_d1(&cb,&wb)?;
    let publics=npudr::verifier::public_inputs(&air,&ci.tape);
    let added=d1::d1_tables(&ci)?;
    let mut traces=Vec::with_capacity(33); let mut tables=Vec::new();
    let mut cells=0usize; let mut failures=0usize;
    for (t,name) in d1::ORDER_D1.iter().enumerate() {
        let extended=d1::render_ext_d1(&ci,name)?;
        let trace=if let Some(tab)=extended {
            TraceCols::from_rows(tab.log,tab.width,|r,buf|buf.copy_from_slice(&tab.cells[r*tab.width..(r+1)*tab.width]))
        } else if t<25 { vp::render_cols(name,&ci.entries[*name])? }
        else {
            let tab=&added[t-25];
            TraceCols::from_rows(tab.log,tab.width,|r,buf|buf.copy_from_slice(&tab.cells[r*tab.width..(r+1)*tab.width]))
        };
        let model=&air.tables[t];
        if trace.width()!=model.width || trace.log_h<1 || trace.log_h>model.max_log {
            return Err(format!("table {t} {name}: shape mismatch").into());
        }
        let bad=npudr::check::failing_constraints_cols(model,&trace,&publics,10);
        failures+=bad.len(); cells+=trace.height()*trace.width();
        eprintln!("table {t:2} {name:9}: log={} width={} bad={}",trace.log_h,trace.width(),bad.len());
        tables.push(json!({"index":t,"name":name,"log_rows":trace.log_h,"rows":trace.height(),
            "width":trace.width(),"compact_bytes":trace.bytes(),"failing_constraints":bad,
            "file":format!("table-{t:02}-{name}.bin")}));
        traces.push(trace);
    }
    let balances=vp::bus_balances(&air,&traces,&publics,&ci.tape).ok_or("public tape does not fit")?;
    let bus_failures:usize=balances.iter().map(|b|b.bad.len()).sum();
    let buses:Vec<_>=balances.iter().map(|b|json!({"bus":b.bus,"messages":b.msgs,"sent":b.sent,
        "received":b.recv,"imbalances":b.bad.len()})).collect();
    fs::create_dir_all(&output)?;
    let accepted=failures==0 && bus_failures==0;
    let dump=args[4]=="--dump";
    let digest=|bytes: &[u8]| format!("{:x}",Sha256::digest(bytes));
    let report=json!({"case":case,"air_source":args[2],"status":if accepted {"PASS"} else {"FAIL"},
        "tables":tables,"buses":buses,"table_count":traces.len(),"total_cells":cells,
        "row_dump_bytes":4*cells+8*traces.len(),"prepared_bytes":ci.tape.len(),"hint_bytes":ci.hint.len(),
        "transactions":ci.run.w.txs.len(),"new_transactions":ci.run.w.new_txs.len(),"operations":ci.run.ops.len(),
        "trace_dumped":accepted && dump,"field_modulus":2013265921u32,
        "compact_trace_bytes":traces.iter().map(TraceCols::bytes).sum::<usize>(),"tx_overhead":ci.ovh,
        "sha256":{"air":digest(air_text.as_bytes()),"claim":digest(&cb),"witness":digest(&wb),
                  "prepared":digest(&ci.tape),"hint":digest(&ci.hint)},
        "encoding":"per-table u32 little-endian: log_rows,width,then row-major canonical cells",
        "scope":"Existing native candidate witness construction and local/exact-bus checks; no succinct proof or formal implementation refinement"});
    if !accepted {
        fs::write(output.join("report.json"),serde_json::to_vec_pretty(&report)?)?;
        return Err("D1 local constraints or bus balance failed".into());
    }
    if dump {
        for (t,trace) in traces.iter().enumerate() {
            let path=output.join(format!("table-{t:02}-{}.bin",d1::ORDER_D1[t]));
            let mut file=BufWriter::new(fs::OpenOptions::new().write(true).create_new(true).open(path)?);
            file.write_all(&(trace.log_h as u32).to_le_bytes())?;
            file.write_all(&(trace.width() as u32).to_le_bytes())?;
            for r in 0..trace.height() { for col in &trace.cols { file.write_all(&col.get(r).to_le_bytes())?; } }
            file.flush()?;
        }
    }
    // Small public/semantic artifacts are useful even without the multi-GB trace dump.
    for (name,bytes) in [("claim.bin",&cb),("prepared.bin",&ci.tape),("hint.bin",&ci.hint)] {
            let mut file=fs::OpenOptions::new().write(true).create_new(true).open(output.join(name))?;
            file.write_all(bytes)?;
    }
    let samples:Vec<_>=traces.iter().enumerate().map(|(index,trace)| {
        let height=trace.height();
        let mut selected=vec![0,1,height/2,height-2,height-1];selected.sort_unstable();selected.dedup();
        let rows:Vec<_>=selected.into_iter().map(|row|json!({"row":row,
            "current":trace.cols.iter().map(|c|c.get(row)).collect::<Vec<_>>(),
            "next":trace.cols.iter().map(|c|c.get((row+1)%height)).collect::<Vec<_>>()})).collect();
        json!({"index":index,"log_rows":trace.log_h,"width":trace.width(),"samples":rows})
    }).collect();
    let mut sample_file=fs::OpenOptions::new().write(true).create_new(true).open(output.join("samples.json"))?;
    sample_file.write_all(&serde_json::to_vec(&samples)?)?;
    fs::write(output.join("report.json"),serde_json::to_vec_pretty(&report)?)?;
    println!("33 tables checked; {} buses balanced; {cells} cells; {} bytes row dumps; dump={dump}",balances.len(),4*cells+264);
    Ok(())
}
