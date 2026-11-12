#!/usr/bin/env python3
"""port-a2x.py SRC DST [k=v ...] -- (agent top) one-pass mechanical arm64 → amd64 substitution of a proof/defs module
(the scaffolding; run lemmas still need hand work). Standard rules: namespace/imports Arm64 → Amd64, `s.sp.toNat` →
`(s.regs 4).toNat`, `X.sp` → `X.regs 4`, g `regs 28` → `regs 14`, `Segment`/`ImplApart` → amd64 names, open line;
extra literal rules `old=new` from the command line (applied first, in order)."""
import sys, re
src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()
for kv in sys.argv[3:]:
    a, b = kv.split("=", 1); t = t.replace(a, b)
rules = [
    ("FvModexp.Proofs.Arm64.", "FvModexp.Proofs.Amd64."), ("FvModexp.Arm64.", "FvModexp.Amd64."),
    ("open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic", "open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic"),
    ("open Janus Janus.Arm64 Janus.GoABI Janus.Tactic", "open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic"),
    ("(arm64)", "(amd64)"), ("Memory.readLE_writeLE", "Janus.Arm64.Memory.readLE_writeLE"),
    ("Memory.accessible_writeLE", "Janus.Arm64.Memory.accessible_writeLE"), ("Memory.readLE_lt", "Janus.Arm64.Memory.readLE_lt"),
]
for a, b in rules: t = t.replace(a, b)
t = t.replace("Janus.Arm64.Janus.Arm64.", "Janus.Arm64.")
t = re.sub(r"\bs\.sp\.toNat\b", "(s.regs 4).toNat", t)
t = re.sub(r"\b([A-Za-z][A-Za-z0-9_']*)\.sp\b", r"\1.regs 4", t)
t = t.replace("(s.regs 28)", "(s.regs 14)").replace("regs 28", "regs 14")
t = re.sub(r"\(impl : List Segment\)", "(impl : List Amd64.Segment)", t)
t = re.sub(r"\(hap : ImplApart ", "(hap : Amd64.ImplApart ", t)
open(dst, "w").write(t)
print("wrote", dst)
