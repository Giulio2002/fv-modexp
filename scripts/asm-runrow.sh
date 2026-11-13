#!/usr/bin/env bash
# asm-runrow.sh ISA ROW : `janus verify` of the row module lean/FvModexp/Proofs/<Arm64|Amd64>/Nat/<ROW>.lean
# (namespace FvModexp.<Isa>.<ROW>: theorem `correctness`, namespace `Witness`: `nonvacuous`) on the RUN extraction
# (`(*bigModExp).Run` of the pinned harness with the Run contract flags; the summaries are proved about that
# extraction), under the project caps (memcap 16G, timeout 900 s), with the provenance-fixed janus binary.
# Appends "isa row verdict wall_s peak_MB" to build/asm-rows.tsv (peak = max(driver scope, verified.json memGuard)).
# JANUS_REPLAY_THREADS=1 (BRIEF 2026-11-13); on a fresh cache run the Warmup row (scripts/verify-all.sh) first.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
isa=$1 row=$2
JANUS=${JANUS:-/srv/janus-ops/v033/bin/janus}
HB=${HARNESS_DIR:-/srv/fv-modexp/build}
export JANUS_CACHE_DIR=${JANUS_CACHE_DIR:-/srv/fv-modexp-ops/cache-asm} LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} JANUS_MEM_MAX=16G JANUS_REPLAY_THREADS=${JANUS_REPLAY_THREADS:-1}
case $isa in arm64) dir=Arm64;; amd64) dir=Amd64;; esac
. scripts/contract-flags.sh
base=build/ex-$isa-Run-base; out=build/ex-$isa-$row; mkdir -p build
log=build/log-$isa-$row; t0=$(date +%s)
if [ ! -f "$base/Extracted.lean" ]; then
  rm -rf "$base"
  $JANUS extract "$HB/harness-$isa" 'github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run' "$base" \
    $(contract_flags Run) --max-functions 100 >"$log" 2>&1 || { echo "extract failed"; tail "$log"; exit 1; }
fi
rm -rf "$out"; cp -r "$base" "$out"; : >"$log"
pf=lean/FvModexp/Proofs/$dir/${ROWDIR:-Nat}/$row.lean
timeout 900 memcap -m 16G $JANUS verify "$out" --proof "$pf" --proof-root lean \
  --theorem "FvModexp.$dir.$row.correctness" --theorem "FvModexp.$dir.$row.Witness.nonvacuous" ${EXTRA_THMS:-} >>"$log" 2>&1 &
bg=$!; peak=0; cg=""
while kill -0 $bg 2>/dev/null; do
  if [ -z "$cg" ]; then p=$(pgrep -f "^$JANUS verify $out " | head -1)
    if [ -n "$p" ]; then c=$(cut -d: -f3 /proc/$p/cgroup 2>/dev/null); case "$c" in */run-*.scope) cg=$c;; esac; fi; fi
  if [ -n "$cg" ] && [ -r /sys/fs/cgroup$cg/memory.peak ]; then v=$(cat /sys/fs/cgroup$cg/memory.peak 2>/dev/null || echo 0); [ "${v:-0}" -gt $peak ] && peak=$v; fi
  sleep 2
done
wait $bg; rc=$?; r=PASS; [ $rc = 0 ] || r=FAIL
jp=$(grep -o '"peakBytes": *[0-9]*' "$out/verified.json" 2>/dev/null | grep -o '[0-9]*$' | sort -n | tail -1)
[ -n "$jp" ] && [ "$jp" -gt "$peak" ] && peak=$jp
grep -qE '^Verified: FvModexp' "$log" || r=FAIL
echo -e "$isa\t$row\t$r\t$(( $(date +%s) - t0 ))\t$(( peak / 1048576 ))" | tee -a build/asm-rows.tsv
grep -E "^(Verified|error|FAILED)|Kernel replay|error:" "$log" | head -20
