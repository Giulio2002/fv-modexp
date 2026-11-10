# sourced by verify-all.sh: `contract_flags Fn` prints the extra `janus extract` flags a row needs (Fn = module name of the row, see docs/COVERAGE.md).
# Runtime calls that are not extracted but covered by a pinned Janus contract (docs/RUNTIME-CONTRACTS.md of Janus v0.2.0).
contract_flags() {
  case "$1" in
    Run) echo "--contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier2 --contract runtime.gcWriteBarrier3 --contract runtime.gcWriteBarrier4 --contract runtime.gcWriteBarrier6 --contract runtime.growslice --contract runtime.makeslice --contract runtime.memclrNoHeapPointers --contract runtime.memmove --contract runtime.newobject --contract sync.(*Pool).Get --contract sync.(*Pool).Put";;
    *) echo "";;   # RequiredGas and its callees extract without contracts (runtime.memmove is extracted, not a contract)
  esac
}

# 0 if Fn has a flags case above or is explicitly listed in scripts/noflags.txt (needs none); 1 otherwise (verify-all FAILS)
contract_known() {
  local d; d="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  [ -n "$(contract_flags "$1")" ] && return 0
  grep -qx "$1" "$d/noflags.txt" 2>/dev/null
}
