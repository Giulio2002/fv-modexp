#!/usr/bin/env bash
# dev-lean-expmc.sh [-x ISA] FILE.lean ... : development compile (agent expmc; adapted from fv-modexp-asm scripts/dev-lean.sh)
# of package modules in dependency order against a private copy of the Janus v0.2.0 framework oleans.
# -x ISA: use the pinned Run extraction of ISA (oleans in $OUT/<ISA>). Prints wall + peak RSS. Development only.
set -e
DEV=/srv/fv-modexp-ops/cache-expmc/dev
isa=arm64
if [ "$1" = "-x" ]; then isa=$2; shift 2; fi
OUT=${OUT:-$DEV/oleans-$isa-031}
pkg=$(cd "$(dirname "${BASH_SOURCE[0]}")/../lean" && pwd)
LP="$OUT:$DEV/${JDIR:-janus031}/.lake/build/lib/lean:$DEV/ethlib/.lake/build/lib/lean:/root/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean"
LEAN=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
for f in "$@"; do
  f=$(realpath "$f")
  case "$(basename "$f")" in
    Extracted.lean) mod=Extracted; root=$(dirname "$f");;
    *) rel=$(realpath --relative-to="$pkg" "$f"); mod=${rel%.lean}; root=$pkg;;
  esac
  mkdir -p "$OUT/$(dirname "$mod")"
  echo "== $mod ($isa)"
  LEAN_PATH="$LP" LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} memcap -m ${CAP:-8G} /usr/bin/time -f "   [%e s, %M KB]" $LEAN -D autoImplicit=false --root="$root" -o "$OUT/$mod.olean" "$f"
done
