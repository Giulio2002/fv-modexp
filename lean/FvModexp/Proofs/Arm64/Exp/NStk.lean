import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64), stack given: `J2` = fn+0x114 → `nat.rem` entry | `J5` = fn+0x324

nat.go:672-681 with `stk ≠ nil`, `len m ≠ 0`: spills of `x`, `y`, `m`, `slow` (`SP' + 296 .. 368`), the defer flag byte
(`SP' + 126`) := 0, then `len y == 1 && y[0] == 1` → `z.rem(stk, x, m)` (stops at `rem`'s entry with `X30` = fn+0x2f0),
else `J5` (`CBZ R11` of nat.go:694). Continuation form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- `nat.rem`'s entry -/
abbrev remA : Nat := 1806400

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem stk (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (sp yp yl n st : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 1048) 384 true = true)
    (hyl : yl < 2 ^ 64) (hn : n < 2 ^ 64) (hst : st < 2 ^ 64) (hn0 : 0 < n) (hst0 : 0 < st) (hy0 : yl ≠ 0)
    (hyp : yp < 2 ^ 64) (hya : M.accessible yp 8 false = true) (hyo : yp + 8 ≤ sp + 1182 ∨ sp + 1425 ≤ yp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1786820) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (hmem : S.mem = M)
    (KR : yl = 1 → M.readLE yp 8 = 1 → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 remA → S'.sp = S.sp →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 →
      S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 10 →
      S'.regs 8 = S.regs 11 → S'.regs 9 = S.regs 12 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 30 = BitVec.ofNat 64 1787296 → S'.mem = M' →
      MemFrame M M' [(sp + 1182, sp + 1183), (sp + 1352, sp + 1425)] → M'.regions = M.regions →
      M'.readLE (sp + 1182) 1 = 0 → Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KD : ¬(yl = 1 ∧ M.readLE yp 8 = 1) → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 1787348 → S'.sp = S.sp →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 →
      S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 →
      S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 →
      S'.regs 12 = S.regs 12 → S'.regs 13 = S.regs 13 → S'.regs 14 = 0#64 → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.mem = M' →
      MemFrame M M' [(sp + 1182, sp + 1183), (sp + 1352, sp + 1425)] → M'.regions = M.regions →
      M'.readLE (sp + 1182) 1 = 0 →
      M'.readLE (sp + 1056 + 296) 8 = (S.regs 4).toNat → M'.readLE (sp + 1056 + 304) 8 = (S.regs 5).toNat →
      M'.readLE (sp + 1056 + 312) 8 = (S.regs 6).toNat → M'.readLE (sp + 1056 + 320) 8 = (S.regs 7).toNat →
      M'.readLE (sp + 1056 + 328) 8 = (S.regs 8).toNat → M'.readLE (sp + 1056 + 336) 8 = (S.regs 9).toNat →
      M'.readLE (sp + 1056 + 344) 8 = (S.regs 10).toNat → M'.readLE (sp + 1056 + 352) 8 = (S.regs 11).toNat →
      M'.readLE (sp + 1056 + 360) 8 = (S.regs 12).toNat → M'.readLE (sp + 1056 + 368) 1 = (S.regs 13).toNat % 256 →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have hy8 : M.readLE yp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  janus_run [] until [remA, 1787348]
  all_goals (try simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint] at *)
  all_goals first
    | (refine KR (by omega) (by janus_assumption) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_)
    | (refine KD (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals first | (janus_simp; done) | skip
  all_goals first
    | (repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1182, sp + 1183)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1352, sp + 1425)) (by simp) (by simp only; omega) (by simp only; omega))
       exact MemFrame.refl _ _)
    | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
        Nat.reduceAdd, h7, h8, h11, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
    | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
        Nat.reduceAdd, h7, h8, h11, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
    | rfl

end FvModexp.Arm64.ExpN
