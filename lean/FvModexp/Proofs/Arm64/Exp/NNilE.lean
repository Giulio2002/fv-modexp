import FvModexp.Proofs.Arm64.Exp.NEpi
import FvModexp.Proofs.Arm64.Exp.NNilT

/-!
# `nat.expNN` (arm64), `stk == nil`: the epilogue with the deferred `stk.free()` (defer flag byte `SP' + 126` = 1)

From a callee return point `r` (`SP' = sp + 1056`): the result stores `SP' + 176..200` (`epi1s`, to `r + 8`), the flag
test (`TBZ` not taken), `MOVB ZR, 127(SP')`, `R26 := 240(SP')` (= `SP' + 216`, the closure record), `R0 := (R26)` (=
`nat.expNN.deferwrap1`), `CALL (R0)` (`epi1c`, to the closure's entry, `X30 = r + 32`), then the closure call (any
`Summary` of it) and the result reloads, `LDP -8(SP')`, `ADD $256`, `RET` (`epi1r`). Continuation form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the result stores: `r` → `r + 8` -/
theorem epi1s (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop) (sp r : Nat) (hr : RetPt r)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 r) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (hacc : S.mem.accessible (sp + 1048) 256 true = true)
    (K : ∀ S1 : State, S1.pc = BitVec.ofNat 64 (r + 8) → S1.sp = S.sp → S1.regs 0 = S.regs 0 →
      S1.regs 1 = S.regs 1 → S1.regs 2 = S.regs 2 → S1.regs 18 = S.regs 18 →
      S1.regs 28 = S.regs 28 → S1.regs 29 = S.regs 29 →
      MemFrame S.mem S1.mem [(sp + 1232, sp + 1256)] → S1.mem.regions = S.mem.regions →
      S1.mem.readLE (sp + 1232) 8 = (S.regs 0).toNat → S1.mem.readLE (sp + 1240) 8 = (S.regs 1).toNat →
      S1.mem.readLE (sp + 1248) 8 = (S.regs 2).toNat →
      Reaches ((LibN.program.link impl).withExit ret0) S1 Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    janus_run [] until [1787304, 1787604, 1787688, 1788040, 1788108]
    refine K _ rfl hsp.symm rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    all_goals first
      | (repeat (first
          | refine MemFrame.writeLE ?_ _ (r := (sp + 1232, sp + 1256)) (by simp) (by simp only; omega) (by simp only; omega))
         exact MemFrame.refl _ _)
      | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
          Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
      | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
          Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]; done)
      | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the flag test (taken: byte `SP' + 126` = 1) and the closure call: `r + 8` → `deferwrap1`'s entry -/
theorem epi1c (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop) (sp r : Nat) (hr : RetPt r)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 (r + 8)) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (hacc : S.mem.accessible (sp + 1048) 256 true = true) (hfl : S.mem.readLE (sp + 1182) 1 = 1)
    (h240 : S.mem.readLE (sp + 1296) 8 = sp + 1272) (h216 : S.mem.readLE (sp + 1272) 8 = dwA)
    (K : ∀ S2 : State, S2.pc = BitVec.ofNat 64 dwA → S2.sp = S.sp → S2.regs 26 = BitVec.ofNat 64 (sp + 1272) →
      S2.regs 30 = BitVec.ofNat 64 (r + 32) → S2.regs 18 = S.regs 18 → S2.regs 28 = S.regs 28 →
      S2.regs 29 = S.regs 29 → MemFrame S.mem S2.mem [(sp + 1183, sp + 1184)] → S2.mem.regions = S.mem.regions →
      Reaches ((LibN.program.link impl).withExit ret0) S2 Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have h240' : S.mem.readLE (sp + 1296) 8 = sp + 1272 := h240
  have h216' : S.mem.readLE (sp + 1272) 8 = 1788272 := h216
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    janus_run [hfl, h240', h216'] until [1788272]
    refine K _ ?_ hsp.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    all_goals first
      | (repeat (first
          | refine MemFrame.writeLE ?_ _ (r := (sp + 1183, sp + 1184)) (by simp) (by simp only; omega) (by simp only; omega))
         exact MemFrame.refl _ _)
      | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc,
          Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h216, h240']; done)
      | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closure call (any summary of `deferwrap1` on `LibN`) and the return: `deferwrap1`'s entry → expNN's return -/
theorem epi1r (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {preD : State → Prop} {postD : State → State → Prop} (hD : Summary (LibN.program.link impl) dwA preD postD)
    (sp r : Nat) (hr : RetPt r) (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 dwA) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h30 : S.regs 30 = BitVec.ofNat 64 (r + 32)) (hpre : preD S)
    (hK : ∀ s3 : State, postD S s3 → s3.mem.regions = S.mem.regions →
      s3.sp = S.sp ∧ s3.mem.accessible (sp + 1048) 256 true = true ∧ s3.mem.readLE (sp + 1056) 8 = ret0 ∧
      ∀ s4 : State, s4.sp = BitVec.ofNat 64 (sp + 1312) →
        s4.regs 0 = BitVec.ofNat 64 (s3.mem.readLE (sp + 1232) 8) →
        s4.regs 1 = BitVec.ofNat 64 (s3.mem.readLE (sp + 1240) 8) →
        s4.regs 2 = BitVec.ofNat 64 (s3.mem.readLE (sp + 1248) 8) →
        s4.regs 29 = BitVec.ofNat 64 (s3.mem.readLE (sp + 1048) 8) →
        s4.regs 18 = s3.regs 18 → s4.regs 28 = s3.regs 28 → s4.mem = s3.mem → F s4) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have es : BitVec.ofNat 64 (sp + 1056) - 8#64 = BitVec.ofNat 64 (sp + 1048) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 1056) + 256#64 = BitVec.ofNat 64 (sp + 1312) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine Reaches.call_regions (hD.withExit hret) hpc hpre fun s3 hpc3 hpost hrg3 => ?_
  obtain ⟨e1, hacc3, h30v, K⟩ := hK s3 hpost hrg3
  rw [h30] at hpc3
  rw [hsp] at e1
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    janus_run [es, es2, h30v]
    refine K _ rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals first | rfl | (janus_simp; done) | skip

end FvModexp.Arm64.ExpN
