#!/usr/bin/env bash
# Dev helper (not used by verify-all): compile proof modules that `import Extracted` against an extraction, outside `janus verify`.
# usage: scripts/dev-lean.sh <isa> <Fn> FILE.lean ...  (Extracted.olean -> build/dev-<isa>-<Fn>/; each FvModexp module -> lean/.lake/build/lib/lean, in order, under memcap 8G)
# Needs: `make build` (lake build FvModexp) done and build/ex-<isa>-<Fn>/Extracted.lean present.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
isa="$1"; fn="$2"; shift 2
out="$root/build/dev-$isa-$fn"; mkdir -p "$out"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
files=(); for f in "$@"; do files+=("$(realpath "$f")"); done
cd "$root/lean"
if [ ! -f "$out/Extracted.olean" ] || [ "$root/build/ex-$isa-$fn/Extracted.lean" -nt "$out/Extracted.olean" ]; then
  LEAN_PATH="$out" lake env lean -R "$root/build/ex-$isa-$fn" -o "$out/Extracted.olean" "$root/build/ex-$isa-$fn/Extracted.lean"
fi
for f in "${files[@]}"; do
  rel="${f#$root/lean/}"; mod="${rel%.lean}"
  lib="$root/lean/.lake/build/lib/lean"; mkdir -p "$lib/$(dirname "$mod")"
  echo "== $rel"
  LEAN_PATH="$out" /usr/bin/time -f "%e s %M KB" memcap -m 8G lake env lean -R "$root/lean" -o "$lib/$mod.olean" "$f"
done
