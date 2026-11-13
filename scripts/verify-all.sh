#!/usr/bin/env bash
# Build the harness for both ISAs, then extract and `janus verify` every row of docs/COVERAGE.md whose status says `verified` for an ISA.
# adapted from fv-uint256 scripts/verify-all.sh.
# Usage: [JANUS=/path/to/janus] scripts/verify-all.sh [FN ...]        (default: all rows in RELEASE ORDER = scripts/release-rows.txt, then the
#        remaining COVERAGE rows; FN = row id = module path with / -> _, e.g. RequiredGas, Nat_DivWRow, Top_RunSucc; LIST_ONLY=1 prints the order)
# Env:   SKIP_WARMUP=1 (skip the cache warm-up), ONLY_ISA=arm64|amd64, ROWS=N (rows in parallel, default 1; the release run uses 6), JANUS_CACHE_DIR (default: a FRESH empty build/jcache-<stamp>;
#        a non-empty dir is refused unless ALLOW_WARM_CACHE=1, a dev-run convenience that is never used for the release), WITNESS (default 1),
#        SKIP_HARNESS=1 (reuse build/harness-*; the hash check still runs), LEAN_NUM_THREADS (default 4), JANUS_JOBS (2).
# SANITY CAPS (project goal, README.md): every row runs under `memcap 16G` and `timeout 900`. They are constants of this script:
# there is deliberately NO environment variable, flag or file that changes them. A row that exceeds a cap is a FAILED row: fix the proof, not the cap.
# Output: build/rows.tsv  (isa fn verdict wall_seconds peak_rss_MB witnesses), build/log-<isa>-<fn>, and a summary.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
readonly ROW_MEMCAP=16G ROW_TIMEOUT=900
# Janus binary: until the Janus PR fix/own-compile-module-data (olean provenance of Lean `module` files, which EthLib uses) is merged and
# released, the default is the fixed v0.2.0 build; the Lean framework is unchanged (lakefile pin 9ff22946). Override with JANUS=...
JANUS_FIXED=/srv/janus-ops/v032/bin/janus
if [ -z "${JANUS:-}" ]; then if [ -x "$JANUS_FIXED" ]; then JANUS="$JANUS_FIXED"; else JANUS=janus; fi; fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" JANUS_JOBS="${JANUS_JOBS:-2}"
# Kernel replay of a row's own modules (leanchecker, one process per module): under the row's memcap 16G Janus sizes the
# replay workers by a 5 GiB-per-worker estimate for 2 threads (cmd/janus/replaybudget.go) -> ONE worker, i.e. the row's
# 50-56 modules replayed one after the other (147-206 s of a 545-629 s RunErr row, agent top s19). Our modules replay in
# <= 3 GB each with one thread, so 1 thread per worker (2 GiB estimate) lets 4 run at once. A Janus option, not a cap.
export JANUS_REPLAY_THREADS="${JANUS_REPLAY_THREADS:-1}"
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
declare -a jobs_isa jobs_fn jobs_sym jobs_mod
# rows: | `full.go.Symbol` | owner | arm64 status | amd64 status | ...   ; `todo`/`in progress` is reported MISSING and fails the run (never skipped silently)
mapfile -t rows < <(grep -E '^\| `' docs/COVERAGE.md)
fail=0
# RELEASE ORDER (top s43; NOTES-conventions "[top s43] RELEASE ORDER"): scripts/release-rows.txt lists every Run-extraction row
# (`ISA DIR/ROW`, proof module lean/FvModexp/Proofs/<Isa>/DIR/ROW.lean) in dependency order, the Top rows last. Those rows run
# first, in that order; a COVERAGE row not listed there (same ISA + module) runs after them. RUN_SYM = the extraction of every listed row.
RUN_SYM='github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run'
declare -A listed
if [ -f "$root/scripts/release-rows.txt" ]; then
  while read -r isa mod _; do
    case "$isa" in ''|\#*) continue;; esac
    [ -z "${ONLY_ISA:-}" ] || [ "$ONLY_ISA" = "$isa" ] || continue
    fn="${mod//\//_}"; listed["$isa:$mod"]=1
    [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
    sym="$RUN_SYM"; [ "$mod" = RequiredGas ] && sym='github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas'
    jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_sym+=("$sym"); jobs_mod+=("$mod")
  done < "$root/scripts/release-rows.txt"
fi
for row in "${rows[@]}"; do
  sym=$(echo "$row" | cut -d'|' -f2 | tr -d ' `')
  st_arm=$(echo "$row" | cut -d'|' -f4 | tr -d ' '); st_amd=$(echo "$row" | cut -d'|' -f5 | tr -d ' ')
  # proof-module name: `module: Name` in the Notes cell, else the last symbol component (without .abi0/.abiinternal), first letter upper-cased
  notes=$(echo "$row" | cut -d'|' -f6-)
  # a module may sit in a subdirectory (`module: Top/RunErr` = lean/FvModexp/Proofs/<Isa>/Top/RunErr.lean); the row id (FN, file names) is its path with `/` -> `_`
  mod=$(echo "$notes" | grep -oE 'module: *`?[A-Za-z0-9_/]+' | head -1 | sed -E 's/module: *`?//')
  if [ -z "$mod" ]; then mod="${sym%.abi0}"; mod="${mod%.abiinternal}"; mod="${mod##*.}"; mod="${mod^}"; fi
  fn="${mod//\//_}"
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  for pair in "arm64:$st_arm" "amd64:$st_amd"; do
    IFS=: read -r isa st <<<"$pair"
    [ -z "${ONLY_ISA:-}" ] || [ "$ONLY_ISA" = "$isa" ] || continue
    [ -z "${listed[$isa:$mod]:-}" ] || continue   # already a release-order row
    case "$st" in
      verified*|partial*) jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_sym+=("$sym"); jobs_mod+=("$mod");;
      todo*|inprogress*|in-progress*) echo "MISSING ($st)" >"build/res/$isa-$fn.pre"; echo "MISSING 0 0 0" >"build/res/$isa-$fn"; fail=1
         jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_sym+=("-"); jobs_mod+=("$mod");;
      *) ;;   # n/a, out of scope
    esac
  done
done

isa_dir() { case "$1" in arm64) echo Arm64;; amd64) echo Amd64;; esac; }
pf_of() {   # pf_of isa fn: the proof module (FnMain.lean, when it exists and holds `theorem correctness`, is the full-spec proof and wins)
  local dir; dir="$(isa_dir "$1")"
  if [ -f "lean/FvModexp/Proofs/$dir/${2}Main.lean" ] && grep -q "theorem correctness" "lean/FvModexp/Proofs/$dir/${2}Main.lean"; then echo "${2}Main"; else echo "$2"; fi
}
run_job() {   # run_job isa fn sym mod   (fn = row id; mod = proof-module path below Proofs/<Isa>; contract flags are keyed by the symbol's function name)
  local isa="$1" fn="$2" sym="$3" mod="$4" cname dir out cflags pf wt mt w r t0 rss tf; export JANUS_MEM_MAX="$ROW_MEMCAP"
  t0=$(date +%s); tf="build/time-$isa-$fn"; rm -f "$tf"; out="build/ex-$isa-$fn"
  dir="$(isa_dir "$isa")"
  cname="${sym%.abi0}"; cname="${cname%.abiinternal}"; cname="${cname##*.}"; cname="${cname^}"
  cflags="$(contract_flags "$cname")"
  if ! contract_known "$cname"; then echo "no contract-flags case for $fn: add it to scripts/contract-flags.sh (or scripts/noflags.txt)" >"build/log-$isa-$fn"; echo "FAIL(no-flags-case) 0 0 0" >"build/res/$isa-$fn"; return; fi
  pf="$(pf_of "$isa" "$mod")"
  if [ ! -f "lean/FvModexp/Proofs/$dir/$pf.lean" ]; then echo "missing proof module lean/FvModexp/Proofs/$dir/$pf.lean" >"build/log-$isa-$fn"; echo "FAIL(no-module) 0 0 0" >"build/res/$isa-$fn"; return; fi
  # every main theorem (`correctness`, `correctness_<x>`) and every existential witness (`Witness.nonvacuous*`, paired by name by Janus)
  mt=(); while IFS= read -r w; do [ -n "$w" ] && mt+=(--theorem "$w"); done < <(python3 "$root/scripts/witness-theorems.py" --mains "lean/FvModexp/Proofs/$dir/$pf.lean")
  [ ${#mt[@]} -gt 0 ] || mt=(--theorem "FvModexp.$dir.${pf##*/}.correctness")
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
  # Janus runs its Lean jobs in systemd scopes of their own (outside the memcap cgroup): the per-job peak it measured
  # (memoryGuard.peakBytes of the reports) is the authoritative number; take the larger of the two.
  local jp; jp=$(python3 -c 'import json,glob,sys
b=0
for f in glob.glob(sys.argv[1]+"/verified.json")+glob.glob(sys.argv[1]+"/verified/*.json"):
    try: b=max(b,int(json.load(open(f)).get("memoryGuard",{}).get("peakBytes",0)))
    except Exception: pass
print(b//1048576)' "$out" 2>/dev/null || echo 0)
  [ "${jp:-0}" -gt "$rss" ] && rss=$jp
  echo "$r $(( $(date +%s) - t0 )) $rss ${#wt[@]}" >"build/res/$isa-$fn"
}
admit() { local l m; l=$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1); m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ "$l" -lt "${MAX_LOAD:-40}" ] && [ "$m" -ge 20 ]; }
# ---- cache warm-up (outside the row caps): build the Janus framework and the consumer dependency closure into the cache once, so that a
# row's 900 s / 16 G caps measure the row's own modules and kernel replay only. The verdict of the warm-up is irrelevant (logged only).
# One warm-up per ISA among the rows (agent top s19): the per-extraction `Extracted`/`JanusTrusted` compile (~85 s for the
# amd64 Run extraction) is not a row's own module either.
if [ -z "${SKIP_WARMUP:-}${LIST_ONLY:-}" ]; then
 wdone=""
 for wi in "${!jobs_sym[@]}"; do
  wsym="${jobs_sym[$wi]}"; wisa="${jobs_isa[$wi]}"
  [ "$wsym" != "-" ] || continue
  case " $wdone " in *" $wisa "*) continue ;; esac
  wdone="$wdone $wisa"
  if [ -n "$wsym" ]; then
    tw=$(date +%s)
    wc="${wsym%.abi0}"; wc="${wc%.abiinternal}"; wc="${wc##*.}"; wc="${wc^}"
    # the warm-up extraction needs the same extract flags as its row (e.g. Run: runtime contracts, --max-functions)
    $JANUS extract "build/harness-$wisa" "$wsym" build/ex-warmup $(contract_flags "$wc") >build/log-warmup 2>&1 &&
      memcap -m "$ROW_MEMCAP" $JANUS verify build/ex-warmup --proof lean/FvModexp/Proofs/Warmup.lean --proof-root lean \
        --theorem FvModexp.Warmup.correctness >>build/log-warmup 2>&1
    if grep -q 'Kernel replay: leanchecker passed' build/log-warmup; then wv=ok; else wv="FAILED: rows will pay the framework build / kernel replay"; fi
    echo "cache warm-up ($wisa): $(( $(date +%s) - tw )) s, $wv (build/log-warmup; not a row)"
  fi
 done
fi
# ---- ROW CAP RULE (BRIEF): all rows share the ONE fresh cache above; Janus's olean store reuses consumer modules compiled by earlier
# rows, so rows run BOTTOM-UP (scripts/row-order.py: by import-closure size) and a row starts only after every row it shares a proof
# module with has finished: the shared modules are then charged to the lower row, and each row's caps measure its own modules.
t_start=$(date +%s)
order=(); declare -A deps_of
while read -r i d; do order+=("$i"); deps_of[$i]="$d"; done < <(
  for i in "${!jobs_fn[@]}"; do
    [ "${jobs_sym[$i]}" = "-" ] && continue
    echo "$i FvModexp/Proofs/$(isa_dir "${jobs_isa[$i]}")/$(pf_of "${jobs_isa[$i]}" "${jobs_mod[$i]}").lean"
  done | python3 "$root/scripts/row-order.py" --keep-order)
deps_done() { local d; [ "${deps_of[$1]}" = "-" ] && return 0
  for d in ${deps_of[$1]//,/ }; do [ -s "build/res/${jobs_isa[$d]}-${jobs_fn[$d]}" ] || return 1; done; }
nreal=0; for i in "${!jobs_sym[@]}"; do [ "${jobs_sym[$i]}" = "-" ] || nreal=$((nreal+1)); done
[ ${#order[@]} -eq "$nreal" ] || { echo "error: scripts/row-order.py produced no order (see above)" >&2; exit 2; }
if [ -n "${LIST_ONLY:-}" ]; then for i in "${order[@]}"; do echo "row ${jobs_isa[$i]} ${jobs_fn[$i]} (after: ${deps_of[$i]})"; done; exit 0; fi
for i in "${order[@]}"; do
  echo "row ${jobs_isa[$i]} ${jobs_fn[$i]} (after: ${deps_of[$i]})"
  while :; do
    [ "$(jobs -rp | wc -l)" -lt "$NPAR" ] && deps_done "$i" && admit && break
    sleep 3
  done
  run_job "${jobs_isa[$i]}" "${jobs_fn[$i]}" "${jobs_sym[$i]}" "${jobs_mod[$i]}" &
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
