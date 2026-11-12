#!/usr/bin/env python3
"""port-a2x-divmc.py SRC DST [old=new ...] -- (agent divmc; extends top's scripts/gen/port-a2x.py) mechanical arm64 → amd64
substitution for the divmc sqr/mul chain: namespaces/imports/open line, `X.sp.toNat` → `(X.regs 4).toNat`, `X.sp` →
`(X.regs 4)`, g `regs 28` → `regs 14`, `winA` → `win` (amd64 posts frame the whole window), Segment/ImplApart names.
Extra literal rules `old=new` (applied first). The result is a SEED: code addresses, registers and run steps are hand work."""
import sys, re
src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()
for kv in sys.argv[3:]:
    a, b = kv.split("=", 1); t = t.replace(a, b)
rules = [
    ("FvModexp.Proofs.Arm64.", "FvModexp.Proofs.Amd64."), ("FvModexp.Arm64.", "FvModexp.Amd64."),
    ("open Janus Janus.Arm64 Janus.GoABI Janus.Tactic", "open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic"),
    ("(arm64)", "(amd64)"), ("Memory.readLE_writeLE", "Janus.Arm64.Memory.readLE_writeLE"),
    ("Memory.accessible_writeLE", "Janus.Arm64.Memory.accessible_writeLE"), ("Memory.readLE_lt", "Janus.Arm64.Memory.readLE_lt"),
    ("Memory.accessible_mono", "Janus.Arm64.Memory.accessible_mono"), ("Memory.accessible_weaken", "Janus.Arm64.Memory.accessible_weaken"),
]
for a, b in rules: t = t.replace(a, b)
t = t.replace("Janus.Arm64.Janus.Arm64.", "Janus.Arm64.")
t = re.sub(r"\b([A-Za-z][A-Za-z0-9_']*)\.sp\.toNat\b", r"(\1.regs 4).toNat", t)
t = re.sub(r"\b([A-Za-z][A-Za-z0-9_']*)\.sp\b", r"(\1.regs 4)", t)
t = t.replace("regs 28", "regs 14")
t = re.sub(r"\bwinA\b", "win", t)
t = re.sub(r"\(impl : List Segment\)", "(impl : List Amd64.Segment)", t)
t = re.sub(r"\(hap : ImplApart ", "(hap : Amd64.ImplApart ", t)
if "set_option autoImplicit false" not in t:
    lines = t.split("\n"); i = 0
    while i < len(lines) and lines[i].startswith("import "): i += 1
    lines.insert(i, "\nset_option autoImplicit false"); t = "\n".join(lines)
open(dst, "w").write(t)
print("wrote", dst)
