import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W4Defs
import FvModexp.Proofs.Arm64.Exp.W4FinDefs
import FvModexp.Proofs.Arm64.Exp.DeferW
import FvModexp.Proofs.Common.ExpNorm

/-!
# window-4 (arm64), the end: `return zz.norm()` (nat.go:1490) with the deferred `stk.restore`

From the join point (entry + 0xbb4: `zz` in `X3..X5` after the final reduction) the inline `norm` loop, the named-result
stores, the call of the open-coded defer closure (`LibWC.deferSum`) and the return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

/-- the norm loop test `CMP $0, R4` -/
abbrev njoin : Nat := segAddr LibW.program fn + 0xbb4
/-- after the norm loop: `CMP R5, R4` -/
abbrev tailPc : Nat := segAddr LibW.program fn + 0xbc8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem tail (impl : List Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (hret : RetAddr (LibW.program.link impl) ret)
    (S : State) (sp g st n0 p l c : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 tailPc) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 p) (h4 : S.regs 4 = BitVec.ofNat 64 l) (h5 : S.regs 5 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hlc : l ≤ c) (hc : c < 2 ^ 64) (he : FinEnv sp g st n0 r29 ret M) :
    Reaches ((LibW.program.link impl).withExit ret) S (IsReturn (FinPost sp g st n0 p l c r18 r29 M)) := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r912, r840, r848, r856, hst1, hst2, hn0, hstw, hstg, rfp, rlr⟩ := he
  have hD := LibWC.deferSum impl hap DeferW.fnW4 (by simp [DeferW.fnW4])
  have eD : segAddr LibW.program DeferW.fnW4 = 1801824 := by decide
  rw [eD] at hD r840
  janus_run [r912, r840, r848, r856, rfp, rlr] calls [hD]
  refine ⟨?sp, ?_, ?_, ?_, ?r0, ?_, ?_, ?st, ?fr⟩
  case sp => dsimp only; apply BitVec.eq_of_toNat_eq; simp; try omega
  case r0 => janus_simp; try (apply BitVec.eq_of_toNat_eq; simp)
  case st => dsimp only; assumption
  case fr => janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- one test of the inline `zz.norm()` loop (nat.go:68-74) from `njoin` with `R4 = l`: either the loop exits to `tailPc`
(`l = 0` or limb `l-1` nonzero) or it goes back to `njoin` with `R4 = l - 1` (limb `l-1` zero). Continuation form. -/
theorem finIter (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (S : State) (sp g p l c : Nat) (r18 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 njoin) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 p) (h4 : S.regs 4 = BitVec.ofNat 64 l) (h5 : S.regs 5 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hl : l < 2 ^ 48) (hpa : l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true))
    (KT : ∀ S' : State, S'.pc = BitVec.ofNat 64 tailPc → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 p → S'.regs 4 = BitVec.ofNat 64 l → S'.regs 5 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.mem = M →
      (l = 0 ∨ M.readLE (p + 8 * (l - 1)) 8 ≠ 0) →
      Reaches ((LibW.program.link impl).withExit ret) S' Q)
    (KL : ∀ S' : State, 0 < l → M.readLE (p + 8 * (l - 1)) 8 = 0 →
      S'.pc = BitVec.ofNat 64 njoin → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 p → S'.regs 4 = BitVec.ofNat 64 (l - 1) → S'.regs 5 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.mem = M →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  rcases hpa with hl0 | ⟨hp48, hacc⟩
  · subst hl0
    janus_run until [njoin, tailPc]
    refine KT _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (Or.inl rfl)
    all_goals first | rfl | (janus_simp; done) | skip
  janus_run until [njoin, tailPc]
  · have hl0 : l = 0 := by omega
    refine KT _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (Or.inl hl0)
    all_goals first | rfl | (janus_simp; done) | skip
  · have hl0 : 0 < l := by omega
    refine KL _ hl0 hbr ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals first | rfl | (janus_simp; done) | skip
    janus_simp; apply BitVec.eq_of_toNat_eq; simp; omega
  · refine KT _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (Or.inr hbr)
    all_goals first | rfl | (janus_simp; done) | skip

/-- the inline `zz.norm()` loop (nat.go:68-74) from the join point, then `tail` -/
theorem fin (impl : List Segment) (hap : ImplApart Extracted.program impl) (ret : Nat)
    (hret : RetAddr (LibW.program.link impl) ret)
    (sp g st n0 p c : Nat) (r18 r29 : BitVec 64) (M : Memory) (hc : c < 2 ^ 64)
    (he : FinEnv sp g st n0 r29 ret M) :
    ∀ (l : Nat) (S : State), S.pc = BitVec.ofNat 64 njoin → S.sp = BitVec.ofNat 64 sp →
      S.regs 3 = BitVec.ofNat 64 p → S.regs 4 = BitVec.ofNat 64 l → S.regs 5 = BitVec.ofNat 64 c →
      S.regs 18 = r18 → S.regs 28 = BitVec.ofNat 64 g → S.mem = M → l ≤ c →
      (l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true)) →
      Reaches ((LibW.program.link impl).withExit ret) S
        (IsReturn (FinPost sp g st n0 p (Expmc.normL M p l) c r18 r29 M)) := by
  intro l
  induction l with
  | zero =>
    intro S hpc hsp h3 h4 h5 h18 h28 hmem hlc hp
    refine finIter impl ret hret _ S sp g p 0 c r18 M hpc hsp h3 h4 h5 h18 h28 hmem (by omega) (Or.inl rfl) ?_ ?_
    · intro S' a1 a2 a3 a4 a5 a6 a7 a8 _
      exact tail impl hap ret hret S' sp g st n0 p 0 c r18 r29 M a1 a2 a3 a4 a5 a6 a7 a8 (by omega) hc he
    · intro _ h; omega
  | succ l ih =>
    intro S hpc hsp h3 h4 h5 h18 h28 hmem hlc hp
    obtain ⟨hp, hacc⟩ := hp.resolve_left (by omega)
    refine finIter impl ret hret _ S sp g p (l + 1) c r18 M hpc hsp h3 h4 h5 h18 h28 hmem (by omega) (Or.inr ⟨hp, hacc⟩) ?_ ?_
    · intro S' a1 a2 a3 a4 a5 a6 a7 a8 hnz
      have hN : Expmc.normL M p (l + 1) = l + 1 := by
        simp only [Expmc.normL]; rw [if_neg]; simpa using hnz
      rw [hN]
      exact tail impl hap ret hret S' sp g st n0 p (l + 1) c r18 r29 M a1 a2 a3 a4 a5 a6 a7 a8 hlc hc he
    · intro S' _ hz a1 a2 a3 a4 a5 a6 a7 a8
      have hN : Expmc.normL M p (l + 1) = Expmc.normL M p l := by
        simp only [Expmc.normL]; rw [if_pos (by simpa using hz)]
      rw [hN]
      exact ih S' a1 a2 a3 a4 a5 a6 a7 a8 (by omega)
        (Or.inr ⟨by omega, M.accessible_sub hacc (Or.inl rfl) (Nat.le_refl _) (by omega)⟩)


end FvModexp.Arm64.W4Loop
