#!/usr/bin/env bash
# dev-lean.sh FILE.lean ... : development compile of package modules (given in dependency order) against the Janus/EthLib build
# of a kept `janus verify` workspace (WS = its consumer dir holding janus/ deps/ root/), oleans into $OUT. Prints time + peak RSS.
# An `Extracted.lean` argument is compiled as module `Extracted`. Not used by verify-all (development only).
set -e
WS=${WS:-$(ls -d /srv/fv-modexp-ops/cache-asm/v1/consumer/*/* | grep -v lock | head -1)}
OUT=${OUT:-/srv/fv-modexp-ops/cache-asm/dev/oleans}
pkg=$(cd "$(dirname "${BASH_SOURCE[0]}")/../lean" && pwd)
LP="$OUT:$WS/janus/.lake/build/lib/lean:$WS/deps/ethlibspec/.lake/build/lib/lean:/root/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean"
LEAN=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
for f in "$@"; do
  f=$(realpath "$f")
  case "$(basename "$f")" in
    Extracted.lean) mod=Extracted; root=$(dirname "$f");;
    *) rel=$(realpath --relative-to="$pkg" "$f"); mod=${rel%.lean}; root=$pkg;;
  esac
  mkdir -p "$OUT/$(dirname "$mod")"
  echo "== $mod"
  LEAN_PATH="$LP" LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} memcap -m ${CAP:-12G} /usr/bin/time -f "   [%e s, %M KB]" $LEAN --root="$root" -o "$OUT/$mod.olean" "$f"
done
