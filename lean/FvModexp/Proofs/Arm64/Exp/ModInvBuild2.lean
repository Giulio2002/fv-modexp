import FvModexp.Proofs.Arm64.Exp.ModInvAfter

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `subMod2N`'s precondition inside a round (agent infra)

`natOne_at`: `natOne` (header and word) is unchanged at every memory the runtime facts describe; `subPre_at`: the
precondition of `z.subMod2N(z, zz, e)` (`SubMod2N.Pre`) from the entry `Pre` and the round facts `Mid`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- a held range outside the function's writes (window, `z`, the stack's writable parts) keeps its bytes -/
theorem held_rt {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    {a k : Nat} (hh : Held R L a k) (hw : Outside a k (winA s (K kc) A)) (hz : Apart zp (8 * zc) a k)
    (hs : StkApart s.mem st a k) (hk : 0 < k) : M.readLE a k = s.mem.readLE a k := by
  obtain ⟨-, hF, hLF, -⟩ := hrt
  rw [List.append_assoc] at hF
  obtain ⟨hs1, hs2⟩ := hs hk
  unfold Apart at hz hs1
  refine held_bytes hh hF hLF fun i hi => ⟨?_, ?_⟩
  · simp only [winA, outside_cons, outside_nil, and_true] at hw ⊢; omega
  · simp only [stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨by omega, by omega, ?_⟩
    rcases Nat.lt_or_ge (stLen s.mem st) (stCap s.mem st) with h | h
    · have := hs2 h; unfold Apart at this; omega
    · omega

set_option maxRecDepth 20000 in
theorem natOne_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hkc : 4608 ≤ kc) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {op : Nat}
    (hone : NatOne R L s.mem op (win s (K kc) A) ∧ Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
      StkApart s.mem st op 8 ∧ StkApart s.mem st natOneA 24) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 240) :
    NatOne R L1 M op (win S' 4608 88) := by
  obtain ⟨⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩, za, zo, so, sa⟩ := hone
  have hK : 240 + kc ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have hLE := hrt.2.2.2.1
  have hF := hrt.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at nwin ow
  have hA : M.readLE natOneA 24 = s.mem.readLE natOneA 24 :=
    held_rt hrt (Or.inr nrt) (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega) za sa
      (by omega)
  have hrd : ∀ j, j + 8 ≤ 24 → M.readLE (natOneA + j) 8 = s.mem.readLE (natOneA + j) 8 := fun j hj =>
    held_rt hrt (Or.inr (nrt.of_sub (by omega) (by omega)))
      (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at za ⊢; omega)
      (fun hk => by
        obtain ⟨h1, h2⟩ := sa (by omega)
        exact ⟨by unfold Apart at h1 ⊢; omega, fun h => by have := h2 h; unfold Apart at this ⊢; omega⟩)
      (by omega)
  have hO : M.readLE op 8 = s.mem.readLE op 8 :=
    held_rt hrt oh (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega) zo so (by omega)
  clear hA
  refine ⟨by rw [show natOneA = natOneA + 0 from rfl, hrd 0 (by omega)]; exact n0, by rw [hrd 8 (by omega)]; exact n8,
    by rw [hrd 16 (by omega)]; exact n16, by rw [hO]; exact nw, by rw [hF.accessible]; exact na, nrt, ?_,
    by rw [hF.accessible]; exact oa, o48, hLE.held oh, ?_⟩
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; omega
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
theorem subPre_at (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) (hkc : 4608 ≤ kc) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    {op : Nat}
    (hone : NatOne R L s.mem op (win s (K kc) A) ∧ Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
      StkApart s.mem st op 8 ∧ StkApart s.mem st natOneA 24) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 240)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {e : Nat} (he1 : 1 ≤ e) (he : e ≤ 2 ^ 15) (hW : SubMod2N.W e ≤ c) (hl : l ≤ 2 ^ 12) (hql : ql ≤ 2 ^ 12)
    (hnz : NatNorm M p l) (hnq : NatNorm M q ql) (hb : SubMod2N.cost e ≤ b1)
    (h30 : (S'.regs 30).toNat % 4 = 0 ∧ (S'.regs 30).toNat < 2 ^ 48) :
    SubMod2N.Pre R b1 L1 op p l c q ql qc e S' := by
  have hK : 240 + kc ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simp only [K] at this; omega
  have hsp' := sp'_eq hsp
  have hone' := hone
  obtain ⟨⟨-, -, -, -, -, nrt, -, -, -, oh, -⟩, za, zo, -, -⟩ := hone'
  obtain ⟨-, hrt, hz, hzz, hap, hlc, hqlc, hnc, hqc⟩ := hmid
  have hz' := hz
  obtain ⟨c40, -, zlive, -, zwin, zg, -, -⟩ := hz'
  obtain ⟨q40, -, qlive, -, qwin, -, -, -⟩ := hzz
  obtain ⟨-, qh, qa, q48⟩ := qlive hqc
  simp only [win, K, A, outside_cons, outside_nil, and_true] at zwin qwin
  unfold SubMod2N.Pre
  rw [hm]
  refine ⟨cenv_at hpre hrt hsp h28 hm hkc (Nat.le_refl _), hpre.2.1, hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    natOne_at hpre hkc hrt hone hsp', own_apart hz (Or.inr nrt) za, own_apart hz oh zo, he1, he, hlc, hW, c40, hl,
    hqlc, q40, hql, zlive, ?_, by rw [h28]; exact zg, hnz, M.accessible_sub qa (Or.inr rfl) (Nat.le_refl _) (by omega), by omega,
    qh.sub (Nat.le_refl _) (by omega), ?_, hnq, hap, hb, by rw [h28]; exact hrt.2.2.2.2.1, h30.1, h30.2⟩
  · simp only [win, hsp', SubMod2N.K, SubMod2N.A, outside_cons, outside_nil, and_true]; omega
  · simp only [win, hsp', SubMod2N.K, SubMod2N.A, outside_cons, outside_nil, and_true]; omega

end

end FvModexp.Arm64.ModInv
