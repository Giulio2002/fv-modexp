#!/usr/bin/env bash
# dev-lean-infra.sh ISA FILE.lean ... : development compile (agent infra) of package modules against the pinned Run
# extraction of ISA, oleans in /srv/fv-modexp-ops/cache-infra/dev/oleans-ISA. Prints wall + peak RSS. Development only.
set -e
isa=$1; shift
OUT=/srv/fv-modexp-ops/cache-infra/dev/oleans-$isa; mkdir -p $OUT
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
X=/srv/fv-modexp/build/x-Run-$isa
cd $root/lean
TC=/root/.elan/toolchains/leanprover--lean4---v4.34.1
LP="$OUT:$root/lean/.lake/packages/janus/.lake/build/lib/lean:$root/lean/.lake/packages/ethlibspec/.lake/build/lib/lean:$TC/lib/lean"
if [ ! -f $OUT/Extracted.olean ]; then
  LEAN_PATH=$LP $TC/bin/lean -R $X -o $OUT/Extracted.olean $X/Extracted.lean
fi
for f in "$@"; do
  case "$f" in /*) ;; *) f=$root/$f;; esac
  f=$(realpath "$f"); rel=${f#$root/lean/}; mod=${rel%.lean}
  mkdir -p "$OUT/$(dirname "$mod")"
  echo "== $mod ($isa)"
  LEAN_PATH=$LP LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} memcap -m ${CAP:-8G} /usr/bin/time -f "   [%e s, %M KB]" \
    $TC/bin/lean -D autoImplicit=false -R $root/lean -o "$OUT/$mod.olean" "$f"
done
