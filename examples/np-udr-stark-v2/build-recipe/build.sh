#!/usr/bin/env bash
# Offline, reproducible build (run by the judge as `bash build-recipe/build.sh`
# from the package root, no network, fresh $HOME, SOURCE_DATE_EPOCH=0).
# Two builds must be bit-identical.
#
#   out/prepare, out/prove  Rust (source/), every crate from source/vendor/
#                           (build-recipe/vendor.sh: crates.io + Plonky3 @
#                           3acc8b7), --locked --offline. The v3 (D0a) entry
#                           points: out/prepare = bin `prepare_v3` (checks the
#                           approved params are NpUdrStarkV2.publicBin, writes
#                           public.bin), out/prove = bin `prove_v3` (the
#                           `npudr v3prove` pipeline: hint + prepD0 + 25
#                           nearAirV3 tables + STARK at auxGroup 2, AIR
#                           source/near-air-v3.json compiled in). The v1 bins
#                           `prepare`/`prove` stay in source/ for the inherited
#                           v1 conformance suite; they are not shipped.
#   out/verify              the Lean verifier model [formal] verifier_model
#                           compiled by the Lean compiler, laid out exactly like
#                           the judge's native-lean build (runners/formal-checker
#                           `native_build`): trusted sources (source/lean-vendor)
#                           + the model's import closure in formal/ (which
#                           includes the vendored zk-formal package
#                           formal/ZkFormal and formal/ReexecV3D0), the
#                           judge-owned main wrapper, one link with no Lake.
#
# Toolchains required in the build image (not shipped): Rust 1.96.0
# (source/rust-toolchain.toml), Lean leanprover/lean4:v4.34.1 (elan).
#
# Rust codegen is pinned to x86-64-v3 (AVX2/BMI2/FMA) + SHA-NI + AES-NI (the
# challenge hardware profile is an AMD Zen 5 host); the binaries do not depend
# on the build host's CPU.
#
# Overrides (developer use; the judge sets none): MODEL_MODULE, MODEL_DECL
# (default: [formal] verifier_model_module / verifier_model of candidate.toml),
# SKIP_LEAN=1 (Rust only).
set -euo pipefail

ROOT="$(pwd)"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
export TZ=UTC LC_ALL=C

# ---- Rust prover ------------------------------------------------------------
# On the judge build the locked dependency graph is vendored into source/vendor
# (build-recipe/vendor.sh) and resolved from there; source replacement lives in
# the (fresh) CARGO_HOME, not in source/.cargo, so that development builds in
# source/ keep resolving from the network. Without source/vendor we build
# against the ambient cargo cache (developer path) and skip the vendored-source
# replacement.
cmp -s source/Cargo.lock dependency-locks/Cargo.lock || {
  echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2
  exit 1
}
if [ -d source/vendor ]; then
  export CARGO_HOME="${HOME}/cargo-home"
  mkdir -p "${CARGO_HOME}"
  cat > "${CARGO_HOME}/config.toml" <<EOF
[source.crates-io]
replace-with = "vendored-sources"

[source."git+https://github.com/Plonky3/Plonky3?rev=3acc8b70e68d6c2afc03930700c26540bd47458d"]
git = "https://github.com/Plonky3/Plonky3"
rev = "3acc8b70e68d6c2afc03930700c26540bd47458d"
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "${ROOT}/source/vendor"

[net]
offline = true
EOF
else
  echo "warning: source/vendor missing (run build-recipe/vendor.sh before packing); using the ambient cargo cache" >&2
fi
export CARGO_NET_OFFLINE=true
cargo_build() {
  ( cd source && env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
      CARGO_BUILD_RUSTFLAGS="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME:-$HOME/.cargo}=/cargo -C strip=symbols -C target-cpu=x86-64-v3 -C target-feature=+sha,+aes" \
      CARGO_TARGET_DIR="${ROOT}/source/target" \
      cargo build --release --locked --offline "$@" )
}
cargo_build --bin prepare_v3 --bin prove_v3 --bin leanorder
mkdir -p out
for bin in prepare prove; do
  install -m 0755 "source/target/release/${bin}_v3" "out/${bin}"
done
[ "${SKIP_LEAN:-0}" = 1 ] && { sha256sum out/prepare out/prove; exit 0; }

# ---- Lean verifier: the judge's native-lean build, replicated --------------
# runners/formal-checker `native_build`: `lean -c` every trusted module (judge
# `topo` order) and the model's import closure (staged-tree topological order,
# filtered to the closure), the judge-owned main wrapper (`ARENACORE_MAIN_
# TEMPLATE`, verbatim in source/verifier/), then `leanc -c -O3 -DNDEBUG` per C
# file and one `leanc -o` link in that order. Object files and the link are
# path-independent, so out/verify is byte-identical to the judge's build.
export PATH="${ELAN_HOME:-${HOME}/.elan}/bin:${PATH}"
toml() { sed -n "s/^${1}[[:space:]]*=[[:space:]]*\"\\([^\"]*\\)\".*/\\1/p" candidate.toml; }
MODEL_MODULE="${MODEL_MODULE:-$(toml verifier_model_module)}"
MODEL_DECL="${MODEL_DECL:-$(toml verifier_model)}"
[ -n "${MODEL_MODULE}" ] && [ -n "${MODEL_DECL}" ] || { echo "candidate.toml: no [formal] verifier_model(_module)" >&2; exit 1; }
[ -d source/lean-vendor ] || { echo "source/lean-vendor missing: run build-recipe/sync-lean.sh before packing" >&2; exit 1; }
( cd source/lean-vendor && find . -type f ! -path './*/.lake/*' | sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/lean-vendor.sha256 || {
  echo "source/lean-vendor differs from dependency-locks/lean-vendor.sha256 (build-recipe/sync-lean.sh)" >&2
  exit 1
}
( cd formal && find ZkFormal ReexecV3D0 -type f -name '*.lean' 2>/dev/null | sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/zk-formal.sha256 || {
  echo "formal/{ZkFormal,ReexecV3D0} differs from dependency-locks/zk-formal.sha256 (build-recipe/sync-lean.sh)" >&2
  exit 1
}
TC="$(cd source/verifier && lean --print-prefix)"
LEAN="${TC}/bin/lean"
LEANC="${TC}/bin/leanc"
ORDER="${ROOT}/source/target/release/leanorder"
# The trusted modules present in source/lean-vendor (the transitive closure of
# the D0a model's trusted imports): ArenaCore, NearSpec, NearSpecV3. This is
# the D0a challenge's `trusted` set; it includes NearSpec.TrieUpsertProofs,
# NearSpecV3.PrepD0 / ChunkValidationV0a / ChallengeD0a, which the signed D0a
# challenge config must list (the draft's near-chunk-v3 list predates them).
TRUSTED_PREFIXES="ArenaCore NearSpec NearSpecV3"
NB="${ROOT}/build-native"
rm -rf "${NB}"
mkdir -p "${NB}/tsrc" "${NB}/msrc" "${NB}/main" "${NB}/olean" "${NB}/c" "${NB}/o"
cp -R source/lean-vendor/formal-core/ArenaCore source/lean-vendor/formal-core/ArenaCore.lean "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/NearSpec "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/v3/NearSpecV3 "${NB}/tsrc/"
TRUSTED="$("${ORDER}" "${NB}/tsrc" ${TRUSTED_PREFIXES})"
MODEL="$("${ORDER}" --closure formal "${MODEL_MODULE}" --trusted "${NB}/tsrc" ${TRUSTED_PREFIXES})"
for m in ${MODEL}; do
  mkdir -p "$(dirname "${NB}/msrc/${m//.//}")"
  cp "formal/${m//.//}.lean" "${NB}/msrc/${m//.//}.lean"
done
sed -e "s/{{model_module}}/${MODEL_MODULE}/" -e "s/{{model_decl}}/${MODEL_DECL}/" \
  source/verifier/ArenaVerifyMain.lean.template > "${NB}/main/ArenaVerifyMain.lean"
export LEAN_PATH="${NB}/olean"
compile() {  # root module
  local root="$1" m="$2" stem="${2//.//}"
  mkdir -p "$(dirname "${NB}/olean/${stem}")"
  "${LEAN}" -R "${root}" -o "${NB}/olean/${stem}.olean" -i "${NB}/olean/${stem}.ilean" \
    -c "${NB}/c/${m}.c" "${root}/${stem}.lean"
}
LINK=()
for m in ${TRUSTED}; do compile "${NB}/tsrc" "$m"; LINK+=("$m"); done
for m in ${MODEL}; do compile "${NB}/msrc" "$m"; LINK+=("$m"); done
compile "${NB}/main" ArenaVerifyMain; LINK+=(ArenaVerifyMain)
objs=()
for m in "${LINK[@]}"; do
  "${LEANC}" -c -O3 -DNDEBUG "${NB}/c/${m}.c" -o "${NB}/o/${m}.o"
  objs+=("${NB}/o/${m}.o")
done
"${LEANC}" -o "${NB}/o/verify" "${objs[@]}"
install -m 0755 "${NB}/o/verify" out/verify
rm -rf "${NB}"
sha256sum out/prepare out/prove out/verify
