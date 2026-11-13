#!/usr/bin/env bash
# asm-row.sh ISA Fn SYMBOL [contract flags...]: extract SYMBOL from the pinned build/harness-ISA (main checkout) and
# `janus verify` lean/FvModexp/{Proofs,Legacy}/<Arm64|Amd64>/<Fn>.lean (theorem correctness + every Witness.nonvacuous*) under the
# project caps (memcap 16G, timeout 900 s). Appends "isa fn verdict wall_s peak_MB" to build/asm-rows.tsv; peak_MB is the
# max(memory.peak of the memcap scope (janus driver), memGuard.peakBytes of verified.json (the sandboxed lake/lean jobs)).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
isa=$1 fn=$2 sym=$3; shift 3
JANUS=${JANUS:-/srv/fv-modexp/build/janus}
HB=${HARNESS_DIR:-/srv/fv-modexp/build}
export JANUS_CACHE_DIR=${JANUS_CACHE_DIR:-/srv/fv-modexp-ops/cache-asm} LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} JANUS_MEM_MAX=16G
case $isa in arm64) dir=Arm64;; amd64) dir=Amd64;; esac
out=build/ex-$isa-$fn; mkdir -p build
pf=lean/FvModexp/Proofs/$dir/$fn.lean
# the retired standalone rows moved to lean/FvModexp/Legacy/<Isa>/ (coordinator 2026-11-15)
[ -f "$pf" ] || pf=lean/FvModexp/Legacy/$dir/$fn.lean
th=(--theorem "FvModexp.$dir.$fn.correctness")
for w in $(python3 - "$pf" <<'PY'
import sys,re
ns=[]
for l in open(sys.argv[1]):
    m=re.match(r'namespace (\S+)',l)
    if m: ns.append(m.group(1)); continue
    m=re.match(r'end (\S+)',l)
    if m and ns and ns[-1]==m.group(1): ns.pop(); continue
    m=re.match(r'theorem _root_\.(\S*Witness\.\w+)',l)
    if m: print(m.group(1)); continue
    m=re.match(r'theorem (correctness_\w+)',l)
    if m: print('.'.join(ns+[m.group(1)])); continue
    m=re.match(r'theorem (nonvacuous\w*)',l)
    if m: print('.'.join(ns+[m.group(1)]))
PY
); do th+=(--theorem "$w"); done
log=build/log-$isa-$fn; t0=$(date +%s)
$JANUS extract "$HB/harness-$isa" "$sym" "$out" "$@" >"$log" 2>&1 || { echo "extract failed"; tail "$log"; exit 1; }
timeout 900 memcap -m 16G $JANUS verify "$out" --proof "$pf" --proof-root lean "${th[@]}" >>"$log" 2>&1 &
bg=$!; peak=0; cg=""
while kill -0 $bg 2>/dev/null; do
  if [ -z "$cg" ]; then p=$(pgrep -f "^$JANUS verify $out " | head -1)
    if [ -n "$p" ]; then c=$(cut -d: -f3 /proc/$p/cgroup 2>/dev/null); case "$c" in */run-*.scope) cg=$c;; esac; fi; fi
  if [ -n "$cg" ] && [ -r /sys/fs/cgroup$cg/memory.peak ]; then v=$(cat /sys/fs/cgroup$cg/memory.peak 2>/dev/null || echo 0); [ "${v:-0}" -gt $peak ] && peak=$v; fi
  sleep 2
done
wait $bg; rc=$?; r=PASS; [ $rc = 0 ] || r=FAIL
# the sandboxed lake/lean jobs run in their own janus-job-*.scope (Janus memguard), outside the memcap scope:
# their peak is recorded by janus in verified.json (memGuard.peakBytes); report the larger of the two
jp=$(grep -o '"peakBytes": *[0-9]*' "$out/verified.json" 2>/dev/null | grep -o '[0-9]*$' | sort -n | tail -1)
[ -n "$jp" ] && [ "$jp" -gt "$peak" ] && peak=$jp
grep -qE '^Verified: FvModexp' "$log" || r=FAIL
echo -e "$isa\t$fn\t$r\t$(( $(date +%s) - t0 ))\t$(( peak / 1048576 ))" | tee -a build/asm-rows.tsv
grep -E "^(Verified|error|FAILED)|Kernel replay|error:" "$log" | head -20
