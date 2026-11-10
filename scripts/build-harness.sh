#!/usr/bin/env bash
# Build the harness binaries under verification: build/harness-{arm64,amd64} from go/ with the pinned toolchain and flags, then check scripts/harness.sha256.
# (geth's own release binaries use Go 1.27.3, which Janus v0.2.0's runtime pins do not cover: go1.26.10 is Janus-pinned and satisfies geth's go.mod.)
# usage: scripts/build-harness.sh [--update-hashes]
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
GO="${GO:-$(command -v go || true)}"; [ -n "$GO" ] || { [ -x /usr/local/go/bin/go ] && GO=/usr/local/go/bin/go; }
[ -n "$GO" ] && [ -x "$GO" ] || { echo "error: no Go toolchain: set GO=/path/to/go (any Go >= 1.21 downloads go1.26.10 itself)" >&2; exit 2; }
mkdir -p build
for a in arm64 amd64; do
  (cd go && GOTOOLCHAIN=go1.26.10 CGO_ENABLED=0 GOOS=linux GOARCH=$a GOAMD64=v1 "$GO" build -trimpath -buildvcs=false -o "../build/harness-$a" ./harness) || { echo "harness build failed ($a)" >&2; exit 2; }
done
if [ "${1:-}" = --update-hashes ]; then
  { sed -n '/^#/p' scripts/harness.sha256; (cd build && sha256sum harness-amd64 harness-arm64); } > scripts/harness.sha256.new && mv scripts/harness.sha256.new scripts/harness.sha256
  echo "updated scripts/harness.sha256"; exit 0
fi
bad=0
while read -r h name; do
  case "$h" in ''|\#*) continue;; esac
  got="$(sha256sum "build/$name" | awk '{print $1}')"
  [ "$got" = "$h" ] || { echo "HARNESS MISMATCH: build/$name has sha256 $got, expected $h (scripts/harness.sha256)" >&2; bad=1; }
done < scripts/harness.sha256
[ $bad = 0 ] && echo "harness OK (hashes match scripts/harness.sha256)"
exit $bad
