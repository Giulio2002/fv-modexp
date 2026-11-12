#!/bin/bash
# scripts/repin-v031.sh REV [JANUS_BIN]   (agent top s20; run from any directory inside the fv-modexp worktree)
#
# ONE command for the Janus v0.3.1 re-pin (BRIEF "RE-PIN TO JANUS v0.3.1 IS REQUIRED FOR THE FINAL ROWS"):
#   1. pin: lean/lakefile.toml janus rev 9ff22946… → REV (the v0.3.1 tag's commit), `lake update janus`, and (if given)
#      JANUS_BIN as verify-all.sh's default binary (JANUS_FIXED);
#   2. delete the local copies of Janus PR #2's contracts (Proofs/{Arm64,Amd64}/{MemmoveZero,MakesliceZero}.lean), drop
#      their imports, map `FvModexp.{Arm64,Amd64}.{MemmoveZeroLive,MakesliceZeroLive,ZeroAllocRet}(64)` to `Janus.Contracts.*`,
#      make sure every user opens `Janus.Contracts`, rename the local `liveMemRet_none(64)` (now also in Janus) to `…L`;
#   3. print the sweep list for the BREAKING alloc-contract change (`Outside et 16 (calleeStack …)` now inside
#      MakeslicePre / NewobjectPre / MallocgcPre / GrowsliceArgs (+64), GrowsliceOld takes the stack bound) — every call
#      site of a makeslice / newobject / mallocgc / growslice contract (`calls [h…]` of janus_run) and every explicit
#      construction / destructuring of those pres — and of the MakesliceZeroLive pre change (its own trailing Outside
#      conjunct is gone: MakeslicePre carries it);
#   4. (BUILD=1) dev-build every Top row module of both ISAs (build/dgen.py), so the failing call sites show up.
# Nothing is committed; review `git diff`, fix the listed sites, then `scripts/verify-all.sh Top_RunOkRow …`.
# DRY=1: only print what would change (steps 1+2) and the sweep list.
set -euo pipefail
REV=${1:?usage: scripts/repin-v031.sh REV [JANUS_BIN]   (REV = full commit of the Janus v0.3.1 tag)}
JB=${2:-}
OLD=9ff22946b804c2bd860c038b34817a4e1a06285b
ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"
DRY=${DRY:-0}
run() { if [ "$DRY" = 1 ]; then echo "DRY: $*"; else eval "$@"; fi; }
[[ "$REV" =~ ^[0-9a-f]{40}$ ]] || { echo "error: REV must be a full 40-hex commit" >&2; exit 2; }
if [ "$DRY" != 1 ] && [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "error: tracked files modified; commit or stash first" >&2; exit 2; fi
L=lean/FvModexp

echo "== 1. pin"
grep -q "rev = \"$OLD\"" lean/lakefile.toml || { echo "error: lakefile.toml does not pin $OLD" >&2; exit 2; }
run "sed -i 's/rev = \"$OLD\"/rev = \"$REV\"/' lean/lakefile.toml"
run "(cd lean && lake update janus)"
if [ -n "$JB" ]; then
  [ -x "$JB" ] || { echo "error: $JB not executable" >&2; exit 2; }
  run "sed -i 's|^JANUS_FIXED=.*|JANUS_FIXED=$JB|' scripts/verify-all.sh"
else
  echo "hint: verify-all.sh still defaults to $(grep '^JANUS_FIXED=' scripts/verify-all.sh) — pass JANUS=<v0.3.1 binary>"
fi
echo "-- other mentions of the old pin (update by hand where they describe the pin):"
git grep -n "9ff22946" -- . ':!lean/lakefile.toml' ':!lean/lake-manifest.json' | head -40 || true

echo "== 2. local PR #2 copies → Janus's"
LOCAL="$L/Proofs/Arm64/MemmoveZero.lean $L/Proofs/Arm64/MakesliceZero.lean $L/Proofs/Amd64/MemmoveZero.lean $L/Proofs/Amd64/MakesliceZero.lean"
for f in $LOCAL; do [ -f "$f" ] && run "git rm -q $f"; done
IMP='^import FvModexp\.Proofs\.(Arm64|Amd64)\.(MemmoveZero|MakesliceZero)$'
for f in $(grep -rlE "$IMP" "$L" --include=*.lean || true); do
  run "sed -i -E '/$IMP/d' $f"
  if [ "$DRY" != 1 ] && ! grep -q '^import ' "$f"; then sed -i '1i import Janus' "$f"; fi
  echo "  import dropped: $f"
done
NAMES='(MemmoveZeroLive|MakesliceZeroLive|ZeroAllocRet)'
for f in $(grep -rlE "FvModexp\.(Arm64|Amd64)\.$NAMES" "$L" --include=*.lean || true); do
  run "sed -i -E 's/FvModexp\.(Arm64|Amd64)\.$NAMES(64)?\b/Janus.Contracts.\2\3/g' $f"
  echo "  qualified names mapped: $f"
done
for f in $(grep -rlE "\b$NAMES(64)?\b" "$L" --include=*.lean || true); do
  if ! grep -qE '^open .*\bJanus\.Contracts\b' "$f"; then
    echo "  WARN no 'open Janus.Contracts' (add it or qualify): $f"
  fi
done
for f in $(grep -rlE '\bliveMemRet_none(64)?\b' "$L" --include=*.lean || true); do
  run "sed -i -E 's/\bliveMemRet_none(64)?\b/liveMemRet_none\1L/g' $f"
  echo "  liveMemRet_none(64) → …L (local copy; Janus now has the same name): $f"
done

echo "== 3. sweep list (BREAKING alloc pres: discharge 'Outside <descriptor> 16 (calleeStack[64] s stack n)')"
echo "-- recipe (Janus CHANGELOG v0.3.1): descriptor is .rodata → 'janus_data hd [hw]' (or the site's hut/hwT/uint8T/errT"
echo "   apart_of_data fact) then 'simp only [calleeStack, outside_cons, outside_nil, and_true]; omega';"
echo "   witnesses: 'by simp only [calleeStack, outside_cons, outside_nil]; decide'; growslice: old array outside the window too."
echo "-- contract hypotheses taken (by file):"
grep -rnE '(MakesliceLiveContract|NewobjectLiveContract|MallocgcLiveContract|GrowsliceLiveContract|MakesliceZeroLive)(64)? ' \
  "$L" --include=*.lean | grep -vE '^\S+:\s*--' | awk -F: '{print $1}' | sort | uniq -c | sort -rn
echo "-- janus_run call sites naming an alloc hypothesis (calls [ … ]):"
grep -rnE "calls \[[^]]*\bh(mk|no|gr)[A-Za-z0-9_']*" "$L" --include=*.lean | sed 's/^\(\S*:[0-9]*\):.*/\1/' | sort -u
echo "-- explicit MakeslicePre / NewobjectPre / MallocgcPre / GrowsliceArgs / GrowsliceOld terms (arity changes):"
grep -rnE '\b(MakeslicePre|NewobjectPre|MallocgcPre|GrowsliceArgs|GrowsliceOld)(64)?\b' "$L" --include=*.lean | \
  sed 's/^\(\S*:[0-9]*\):.*/\1/' | sort -u
echo "-- MakesliceZeroLive pre (trailing Outside conjunct removed; it is MakeslicePre's last conjunct now):"
grep -rnE 'MakesliceZeroLive(64)?\b' "$L" --include=*.lean | grep -v 'def \|theorem .*of_codeIn' | \
  sed 's/^\(\S*:[0-9]*\):.*/\1/' | sort -u

if [ "${BUILD:-0}" = 1 ] && [ "$DRY" != 1 ]; then
  echo "== 4. dev build (both ISAs, Top rows)"
  J=${J:-2} python3 build/dgen.py arm64 FvModexp.Proofs.Arm64.Top.RunOkRow FvModexp.Proofs.Arm64.Top.RunErr | tail -20
  J=${J:-2} python3 build/dgen.py amd64 FvModexp.Proofs.Amd64.Top.RunOkRow FvModexp.Proofs.Amd64.Top.RunErr | tail -20
fi
echo "== done: review 'git diff', fix the sweep sites, rebuild (BUILD=1), then run the rows (scripts/verify-all.sh)."
