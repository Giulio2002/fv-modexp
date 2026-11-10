#!/usr/bin/env bash
# asm-row.sh ISA Fn SYMBOL [contract flags...]: extract SYMBOL from the pinned build/harness-ISA (main checkout) and
# `janus verify` lean/FvModexp/Proofs/<Arm64|Amd64>/<Fn>.lean (theorem correctness + every Witness.nonvacuous*) under the
# project caps (memcap 16G, timeout 900 s). Appends "isa fn verdict wall_s peak_MB" to build/asm-rows.tsv; peak_MB is the
# memory.peak of the memcap cgroup (whole process tree, sandboxed Lean included).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
isa=$1 fn=$2 sym=$3; shift 3
JANUS=${JANUS:-/srv/fv-modexp/build/janus}
HB=${HARNESS_DIR:-/srv/fv-modexp/build}
export JANUS_CACHE_DIR=${JANUS_CACHE_DIR:-/srv/fv-modexp-ops/cache-asm} LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} JANUS_MEM_MAX=16G
case $isa in arm64) dir=Arm64;; amd64) dir=Amd64;; esac
out=build/ex-$isa-$fn; mkdir -p build
pf=lean/FvModexp/Proofs/$dir/$fn.lean
th=(--theorem "FvModexp.$dir.$fn.correctness")
for w in $(grep -oE '^theorem nonvacuous[A-Za-z0-9_]*' "$pf" | awk '{print $2}'); do th+=(--theorem "FvModexp.$dir.$fn.Witness.$w"); done
log=build/log-$isa-$fn; t0=$(date +%s)
$JANUS extract "$HB/harness-$isa" "$sym" "$out" "$@" >"$log" 2>&1 || { echo "extract failed"; tail "$log"; exit 1; }
timeout 900 memcap -m 16G $JANUS verify "$out" --proof "$pf" --proof-root lean "${th[@]}" >>"$log" 2>&1 &
bg=$!; peak=0; cg=""
while kill -0 $bg 2>/dev/null; do
  if [ -z "$cg" ]; then p=$(pgrep -P $bg -f "janus verify" | head -1); [ -n "$p" ] && cg=$(cut -d: -f3 /proc/$p/cgroup 2>/dev/null); fi
  if [ -n "$cg" ] && [ -r /sys/fs/cgroup$cg/memory.peak ]; then v=$(cat /sys/fs/cgroup$cg/memory.peak 2>/dev/null || echo 0); [ "${v:-0}" -gt $peak ] && peak=$v; fi
  sleep 2
done
wait $bg; rc=$?; r=PASS; [ $rc = 0 ] || r=FAIL
grep -qE '^Verified: FvModexp' "$log" || r=FAIL
echo -e "$isa\t$fn\t$r\t$(( $(date +%s) - t0 ))\t$(( peak / 1048576 ))" | tee -a build/asm-rows.tsv
grep -E "^(Verified|error|FAILED)|Kernel replay|error:" "$log" | head -20
