#!/usr/bin/env python3
"""gen-run-de64.py -- (agent top) generate lean/FvModexp/Proofs/Amd64/Top/RunDE{0,1,2}.lean (the operand setBytes
segment pcE j -> pcD (j+1)) from scripts/RunDE64.tmpl. Edit the template, rerun."""
import os
d = os.path.dirname(os.path.abspath(__file__))
t = open(f"{d}/RunDE64.tmpl").read()
RET = {0: "0x654a65", 1: "0x654bf9", 2: "0x654d5b"}
ZERO = """    intro _
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [opAt]; first | (janus64_simp; done) |
      (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
        Nat.zero_div, Nat.zero_mod, hx15]; done) | (janus64_simp [hx15]))"""
NOZERO = "    exact fun h => absurd h (by decide)"
TRANS = """    · refine OpDone.transport (hop {i} (by omega)) ?_ ?_ ?_ ?_
        ((hLFS.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) (hext2.liveSep hLsL1 hwrt))
          (fun _ _ h => hext2.inRanges_old h))) (fun _ _ h => hext2.inRanges_old h)
      all_goals (simp only [opAt]; janus64_simp)"""
for j in range(3):
    s = t.replace("@J@", str(j)).replace("@J1@", str(j + 1)).replace("@RET@", RET[j])
    s = s.replace("@NEXTDOC@", ", and operand %d's `big.Int` is zeroed" % (j + 1) if j < 2 else "")
    s = s.replace("@ZEROPROOF@", ZERO if j < 2 else NOZERO)
    s = s.replace("@JCASES@", " ∨ ".join(f"j = {i}" for i in range(j + 1)))
    s = s.replace("@JPATS@", " | ".join("rfl" for _ in range(j + 1)))
    s = s.replace("@OLDPROOF@\n", "".join(TRANS.format(i=i) + "\n" for i in range(j)))
    if j == 0:
        ap = "    exact opsApart_one _ _"
    else:
        cs = " ∨ ".join(f"i = {i}" for i in range(j)); ps = " | ".join("rfl" for _ in range(j))
        ap = f"""    refine OpsApart.step' (p2 := p1) (c2 := c1) hopA (fun i hi => by
        rcases (show {cs} by omega) with {ps} <;>
          exact ⟨by simp only [opAt]; janus64_simp, by simp only [opAt]; janus64_simp⟩)
      (fun i hi hc => opDone_inRanges (hop i hi) hc) (by janus64_simp [hp1, opAt]) (by janus64_simp [hc1, opAt]) ?_
    intro hc
    rcases hor2 with ⟨-, h⟩ | ⟨-, h⟩
    · simp at h; omega
    · exact h"""
    s = s.replace("@APARTPROOF@", ap)
    open(f"{d}/../lean/FvModexp/Proofs/Amd64/Top/RunDE{j}.lean", "w").write(s)
print("ok")
