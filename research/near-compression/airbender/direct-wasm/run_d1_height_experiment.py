#!/usr/bin/env python3
"""Reproduce isolated D1 padding-height experiment; never runs the FRI prover."""
import argparse, json, os, pathlib, shutil, subprocess, sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument("source",type=pathlib.Path)
p.add_argument("case",type=pathlib.Path)
p.add_argument("air",type=pathlib.Path)
p.add_argument("output",type=pathlib.Path)
p.add_argument("scratch",type=pathlib.Path)
p.add_argument("--baseline",type=pathlib.Path)
p.add_argument("--mrk",action="store_true",help="also parameterize complete-block Merkle height")
a=p.parse_args();here=pathlib.Path(__file__).resolve().parent
scratch=a.scratch.resolve();scratch.mkdir(exist_ok=False)
fork=scratch/"source";build=scratch/"build";build.mkdir()
subprocess.run([sys.executable,str(here/"prepare_d1_height_source.py"),str(a.source.resolve()),str(fork)],check=True)
if a.mrk:
 subprocess.run([sys.executable,str(here/"prepare_d1_mrk_height.py"),str(fork)],check=True)
manifest={"package":{"name":"near-d1-trace-export-research","version":"0.0.0","edition":"2024"}}
# JSON quoted strings are also valid TOML basic strings for these paths.
q=lambda x:json.dumps(str(x))
(build/"Cargo.toml").write_text('[package]\nname="near-d1-trace-export-research"\nversion="0.0.0"\nedition="2024"\n[workspace]\n[dependencies]\nnp-udr-stark={path='+q(fork)+'}\nserde_json="1"\nsha2="0.10"\n[[bin]]\nname="near-d1-trace-export"\npath='+q(here/("near_d1_mrk_height_export.rs" if a.mrk else "near_d1_height_export.rs"))+'\n[profile.release]\nopt-level=2\nlto=false\ncodegen-units=8\n')
with (build/"Cargo.toml").open("a") as manifest:
 manifest.write('\n[[bin]]\nname="near-d1-height-capacity"\npath='+q(here/"near_d1_height_capacity.rs")+'\n')
if a.mrk:
 with (build/"Cargo.toml").open("a") as manifest:
  manifest.write('\n[[bin]]\nname="near-d1-mrk-capacity"\npath='+q(here/"near_d1_mrk_capacity.rs")+'\n')
shutil.copyfile(here/"d1-trace-export/Cargo.lock",build/"Cargo.lock")
env=dict(os.environ,HEAVY_MEM="8G",CARGO_BUILD_JOBS="2",RAYON_NUM_THREADS="2")
wrapper=["taskset","-c","8-15,24-31","/data/illia/nearproof-deps/bin/heavy"]
with (scratch/"build.log").open("w") as log:
 subprocess.run(wrapper+["cargo","+1.96.0","build","--release","--offline","--locked","--manifest-path",str(build/"Cargo.toml")],env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
target=pathlib.Path(env.get("CARGO_TARGET_DIR",str(build/"target")))
subprocess.run(wrapper+[str(target/"release/near-d1-height-capacity"),str(a.case.resolve()),str(scratch/"capacity.json")],env=env,check=True)
if a.mrk:
 subprocess.run(wrapper+[str(target/"release/near-d1-mrk-capacity"),str(a.case.resolve()),str(scratch/"mrk-capacity.json")],env=env,check=True)
with (scratch/"run.log").open("w") as log:
 subprocess.run(wrapper+["/usr/bin/time","-v",str(target/"release/near-d1-trace-export"),str(a.case.resolve()),str(a.air.resolve()),str(a.output.resolve()),"--check-only"],env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
r=json.loads((a.output/"report.json").read_text())
assert r["status"]=="PASS" and r["table_count"]==33
if a.baseline:
 b=json.loads(a.baseline.read_text())
 assert r["buses"]==b["buses"],"native bus counts changed"
 assert r["sha256"]==b["sha256"],"AIR or statement artifacts changed"
 print("PASS: all native checks; baseline bus counts and statement hashes identical")
print(json.dumps({k:r[k] for k in ["height_plan","total_cells","compact_trace_bytes","row_dump_bytes"]},indent=2))
