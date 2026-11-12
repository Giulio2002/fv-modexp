import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Arm64.Nat.Free

/-!
# `nat.expNN` (arm64), `stk == nil`: `J2` = fn+0x114 → `sync.(*Pool).Get` entry (`getStack()`)

nat.go:672-678 with `stk == nil` (`CBZ R3` at fn+0x210 taken): the spills of `x`, `y`, `m`, `slow` (`SP' + 296 .. 368`)
and of `z` (`SP' + 208, 152, 168`), then `CALL sync.(*Pool).Get(&stackPool)` (stops at the contract with
`X30` = fn+0x234). Continuation form (`KG`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- `sync.(*Pool).Get` -/
abbrev getA : Nat := Extracted.program.contractAddr "sync.(*Pool).Get"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem stkNil (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (sp yp yl n st : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 1048) 384 true = true)
    (hyl : yl < 2 ^ 64) (hn : n < 2 ^ 64) (hst : st < 2 ^ 64) (hn0 : 0 < n) (hst0 : st = 0) (hy0 : yl ≠ 0)
    (hyp : yp < 2 ^ 64) (hya : M.accessible yp 8 false = true) (hyo : yp + 8 ≤ sp + 1182 ∨ sp + 1425 ≤ yp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1786820) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (hmem : S.mem = M)
    (KG : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 getA → S'.sp = S.sp → S'.regs 0 = BitVec.ofNat 64 Free.poolA →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 30 = BitVec.ofNat 64 1787108 → S'.mem = M' →
      MemFrame M M' [(sp + 1208, sp + 1216), (sp + 1224, sp + 1232), (sp + 1264, sp + 1272), (sp + 1352, sp + 1425)] →
      M'.regions = M.regions →
      M'.readLE (sp + 1056 + 208) 8 = (S.regs 0).toNat → M'.readLE (sp + 1056 + 152) 8 = (S.regs 1).toNat →
      M'.readLE (sp + 1056 + 168) 8 = (S.regs 2).toNat →
      M'.readLE (sp + 1056 + 296) 8 = (S.regs 4).toNat → M'.readLE (sp + 1056 + 304) 8 = (S.regs 5).toNat →
      M'.readLE (sp + 1056 + 312) 8 = (S.regs 6).toNat → M'.readLE (sp + 1056 + 320) 8 = (S.regs 7).toNat →
      M'.readLE (sp + 1056 + 328) 8 = (S.regs 8).toNat → M'.readLE (sp + 1056 + 336) 8 = (S.regs 9).toNat →
      M'.readLE (sp + 1056 + 344) 8 = (S.regs 10).toNat → M'.readLE (sp + 1056 + 352) 8 = (S.regs 11).toNat →
      M'.readLE (sp + 1056 + 360) 8 = (S.regs 12).toNat → M'.readLE (sp + 1056 + 368) 1 = (S.regs 13).toNat % 256 →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have hy8 : M.readLE yp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  janus_run [] until [getA]
  all_goals (try simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint] at *)
  all_goals refine KG _ _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals first
    | (repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1208, sp + 1216)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1224, sp + 1232)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1264, sp + 1272)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 1352, sp + 1425)) (by simp) (by simp only; omega) (by simp only; omega))
       exact MemFrame.refl _ _)
    | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
        Nat.reduceAdd, h7, h8, h11, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
    | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
        Nat.reduceAdd, h7, h8, h11, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
    | rfl

end FvModexp.Arm64.ExpN
