#!/usr/bin/env bash
# Build the harness for both ISAs, then extract and `janus verify` every row of docs/COVERAGE.md whose status says `verified` for an ISA.
# adapted from fv-uint256 scripts/verify-all.sh.
# Usage: JANUS=/path/to/janus scripts/verify-all.sh [FN ...]        (default: all rows; FN = row function name, e.g. RequiredGas)
# Env:   ONLY_ISA=arm64|amd64, ROWS=N (rows in parallel, default 1; the release run uses 6), JANUS_CACHE_DIR (default: a FRESH empty build/jcache-<stamp>;
#        a non-empty dir is refused unless ALLOW_WARM_CACHE=1, a dev-run convenience that is never used for the release), WITNESS (default 1),
#        SKIP_HARNESS=1 (reuse build/harness-*; the hash check still runs), LEAN_NUM_THREADS (default 4), JANUS_JOBS (2).
# SANITY CAPS (project goal, README.md): every row runs under `memcap 16G` and `timeout 900`. They are constants of this script:
# there is deliberately NO environment variable, flag or file that changes them. A row that exceeds a cap is a FAILED row: fix the proof, not the cap.
# Output: build/rows.tsv  (isa fn verdict wall_seconds peak_rss_MB witnesses), build/log-<isa>-<fn>, and a summary.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
readonly ROW_MEMCAP=16G ROW_TIMEOUT=900
JANUS="${JANUS:-janus}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" JANUS_JOBS="${JANUS_JOBS:-2}"
WITNESS="${WITNESS:-1}"; NPAR="${ROWS:-1}"
command -v memcap >/dev/null || { echo "error: memcap not found (every row must run under a memory cap)" >&2; exit 2; }
command -v "$JANUS" >/dev/null || { echo "error: janus binary not found (JANUS=...)" >&2; exit 2; }
# a FRESH cache: a cache built against another pin/extractor can poison kernel replay
if [ -z "${JANUS_CACHE_DIR:-}" ]; then JANUS_CACHE_DIR="$root/build/jcache-$(date +%Y%m%d-%H%M%S)"; fi
mkdir -p "$JANUS_CACHE_DIR"
if [ -n "$(ls -A "$JANUS_CACHE_DIR" 2>/dev/null)" ] && [ -z "${ALLOW_WARM_CACHE:-}" ]; then
  echo "error: JANUS_CACHE_DIR=$JANUS_CACHE_DIR is not empty: the release run needs a fresh cache (ALLOW_WARM_CACHE=1 for a dev run)" >&2; exit 2; fi
export JANUS_CACHE_DIR
echo "verify-all: JANUS=$JANUS ($(sha256sum "$(command -v "$JANUS")" | cut -c1-16)) cache=$JANUS_CACHE_DIR rows-parallel=$NPAR caps=memcap $ROW_MEMCAP + timeout $ROW_TIMEOUT s witness=$WITNESS"
mkdir -p build
python3 "$root/scripts/check-spec-closure" --structure-only || { echo "check-spec-closure --structure-only failed" >&2; exit 2; }
if [ ! -d lean/.lake/packages/janus ]; then (cd lean && lake update) || { echo "lake update failed" >&2; exit 2; }; fi
. "$root/scripts/contract-flags.sh"
if [ -z "${SKIP_HARNESS:-}" ]; then bash scripts/build-harness.sh >/dev/null || { echo "harness build failed" >&2; exit 2; }; fi
# the binary under verification is pinned (checked even with SKIP_HARNESS): FAIL LOUDLY on a mismatch
hbad=0
while read -r h name; do
  case "$h" in ''|\#*) continue;; esac
  got="$(sha256sum "build/$name" 2>/dev/null | awk '{print $1}')"
  [ "$got" = "$h" ] || { echo "HARNESS MISMATCH: build/$name has sha256 ${got:-<missing>}, expected $h (scripts/harness.sha256)." >&2; hbad=1; }
done < "$root/scripts/harness.sha256"
[ "$hbad" = 0 ] || exit 3

# ---- row jobs: one per (ISA, function); results in build/res/<isa>-<fn> as "VERDICT seconds peakRSS_MB witnesses" ----
rm -rf build/res; mkdir -p build/res
declare -a jobs_isa jobs_fn jobs_sym
# rows: | `full.go.Symbol` | owner | arm64 status | amd64 status | ...   ; `todo`/`in progress` is reported MISSING and fails the run (never skipped silently)
mapfile -t rows < <(grep -E '^\| `' docs/COVERAGE.md)
fail=0
for row in "${rows[@]}"; do
  sym=$(echo "$row" | cut -d'|' -f2 | tr -d ' `')
  st_arm=$(echo "$row" | cut -d'|' -f4 | tr -d ' '); st_amd=$(echo "$row" | cut -d'|' -f5 | tr -d ' ')
  # proof-module name: `module: Name` in the Notes cell, else the last symbol component (without .abi0/.abiinternal), first letter upper-cased
  notes=$(echo "$row" | cut -d'|' -f6-)
  fn=$(echo "$notes" | grep -oE 'module: *`?[A-Za-z0-9_]+' | head -1 | sed -E 's/module: *`?//')
  if [ -z "$fn" ]; then fn="${sym%.abi0}"; fn="${fn%.abiinternal}"; fn="${fn##*.}"; fn="${fn^}"; fi
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  for pair in "arm64:$st_arm" "amd64:$st_amd"; do
    IFS=: read -r isa st <<<"$pair"
    [ -z "${ONLY_ISA:-}" ] || [ "$ONLY_ISA" = "$isa" ] || continue
    case "$st" in
      verified*|partial*) jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_sym+=("$sym");;
      todo*|inprogress*|in-progress*) echo "MISSING ($st)" >"build/res/$isa-$fn.pre"; echo "MISSING 0 0 0" >"build/res/$isa-$fn"; fail=1
         jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_sym+=("-");;
      *) ;;   # n/a, out of scope
    esac
  done
done

run_job() {   # run_job isa fn sym
  local isa="$1" fn="$2" sym="$3" dir out cflags pf wt mt w r t0 rss tf; export JANUS_MEM_MAX="$ROW_MEMCAP"
  t0=$(date +%s); tf="build/time-$isa-$fn"; rm -f "$tf"; out="build/ex-$isa-$fn"
  case "$isa" in arm64) dir=Arm64;; amd64) dir=Amd64;; esac
  cflags="$(contract_flags "$fn")"
  if ! contract_known "$fn"; then echo "no contract-flags case for $fn: add it to scripts/contract-flags.sh (or scripts/noflags.txt)" >"build/log-$isa-$fn"; echo "FAIL(no-flags-case) 0 0 0" >"build/res/$isa-$fn"; return; fi
  # FnMain.lean, when it exists and holds `theorem correctness`, is the full-spec proof and wins over Fn.lean
  pf="$fn"; if [ -f "lean/FvModexp/Proofs/$dir/${fn}Main.lean" ] && grep -q "theorem correctness" "lean/FvModexp/Proofs/$dir/${fn}Main.lean"; then pf="${fn}Main"; fi
  if [ ! -f "lean/FvModexp/Proofs/$dir/$pf.lean" ]; then echo "missing proof module lean/FvModexp/Proofs/$dir/$pf.lean" >"build/log-$isa-$fn"; echo "FAIL(no-module) 0 0 0" >"build/res/$isa-$fn"; return; fi
  # every main theorem (`correctness`, `correctness_<x>`) and every existential witness (`Witness.nonvacuous*`, paired by name by Janus)
  mt=(); while IFS= read -r w; do [ -n "$w" ] && mt+=(--theorem "$w"); done < <(python3 "$root/scripts/witness-theorems.py" --mains "lean/FvModexp/Proofs/$dir/$pf.lean")
  [ ${#mt[@]} -gt 0 ] || mt=(--theorem "FvModexp.$dir.$pf.correctness")
  wt=(); if [ "$WITNESS" != 0 ]; then while IFS= read -r w; do [ -n "$w" ] && wt+=(--theorem "$w"); done < <(python3 "$root/scripts/witness-theorems.py" "lean/FvModexp/Proofs/$dir/$pf.lean"); fi
  r=FAIL
  if $JANUS extract "build/harness-$isa" "$sym" "$out" $cflags >"build/log-$isa-$fn" 2>&1; then
    timeout "$ROW_TIMEOUT" memcap -m "$ROW_MEMCAP" $JANUS verify "$out" --proof "lean/FvModexp/Proofs/$dir/$pf.lean" --proof-root lean \
       "${mt[@]}" "${wt[@]}" >>"build/log-$isa-$fn" 2>&1 &
    local bg=$! peak=0 cg="" p c v
    # peak RSS of the WHOLE row (janus + sandboxed Lean): memory.peak of the memcap cgroup (adapted from asm's scripts/asm-row.sh)
    while kill -0 $bg 2>/dev/null; do
      if [ -z "$cg" ]; then p=$(pgrep -f "^$JANUS verify $out " | head -1)
        if [ -n "$p" ]; then c=$(cut -d: -f3 /proc/$p/cgroup 2>/dev/null); case "$c" in */run-*.scope) cg=$c;; esac; fi; fi
      if [ -n "$cg" ] && [ -r "/sys/fs/cgroup$cg/memory.peak" ]; then v=$(cat "/sys/fs/cgroup$cg/memory.peak" 2>/dev/null || echo 0); [ "${v:-0}" -gt "$peak" ] && peak=$v; fi
      sleep 2
    done
    if wait $bg; then r=PASS; fi
    echo $(( peak / 1024 )) > "$tf"
  fi
  # every row must audit as a run-claiming function spec: runFree / refutation reports FAIL the row
  if [ "$r" = PASS ] && { grep -rEqs '"(runFree|refutation)": *true' "$out/verified.json" "$out/verified" 2>/dev/null || grep -Eqs 'Non-vacuity: Verified \((run-free|refutation)' "build/log-$isa-$fn"; }; then
    echo "FAIL: the audit reports runFree=true or refutation=true for $isa $fn" >>"build/log-$isa-$fn"; r="FAIL(runFree-or-refutation)"
  fi
  if [ "$r" = FAIL ] && grep -qE 'Terminated|timed out|Killed|out of memory' "build/log-$isa-$fn"; then r="FAIL(cap)"; fi
  rss=0; [ -s "$tf" ] && rss=$(( $(tail -1 "$tf" | tr -dc 0-9) / 1024 ))
  echo "$r $(( $(date +%s) - t0 )) $rss ${#wt[@]}" >"build/res/$isa-$fn"
}
admit() { local l m; l=$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1); m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ "$l" -lt "${MAX_LOAD:-40}" ] && [ "$m" -ge 20 ]; }
t_start=$(date +%s)
for i in "${!jobs_fn[@]}"; do
  [ "${jobs_sym[$i]}" = "-" ] && continue
  while :; do
    [ "$(jobs -rp | wc -l)" -lt "$NPAR" ] && admit && break
    sleep 3
  done
  run_job "${jobs_isa[$i]}" "${jobs_fn[$i]}" "${jobs_sym[$i]}" &
  sleep 1
done
wait
# ---- summary and build/rows.tsv ----
printf 'isa\tfunction\tverdict\twall_s\tpeak_rss_mb\twitnesses\n' > build/rows.tsv
for i in "${!jobs_fn[@]}"; do
  isa="${jobs_isa[$i]}"; fn="${jobs_fn[$i]}"
  if [ -s "build/res/$isa-$fn" ]; then read -r r s m nw <"build/res/$isa-$fn"; else r="FAIL(no-result)"; s=0; m=0; nw=0; fi
  case "$r" in PASS) ;; *) fail=1;; esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$isa" "$fn" "$r" "$s" "$m" "${nw:-0}" >> build/rows.tsv
done
echo "== rows (build/rows.tsv): isa function verdict wall_s peak_rss_MB witnesses =="; column -t -s$'\t' build/rows.tsv
echo "== total wall $(( $(date +%s) - t_start )) s, harness hashes OK, caps memcap $ROW_MEMCAP / timeout $ROW_TIMEOUT s, cache $JANUS_CACHE_DIR =="
exit $fail
