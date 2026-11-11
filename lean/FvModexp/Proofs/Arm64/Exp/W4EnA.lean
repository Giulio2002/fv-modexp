import FvModexp.Proofs.Arm64.Exp.W4EnDefs

/-!
# window-4 entry (arm64): entry → the `slices.Grow` decision (fn+0x0 .. fn+0xbc)

`enA`: prologue, spills, defer record, `nr = rnd(23n)`; then either the join `enJ` (`len + nr ≤ cap`, no growth) or
the entry of `growslice(w, len + nr, cap, len + nr - cap, Word)` (return `grRet`). Continuation form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enA (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0)
    (Q : Outcome → Prop) (sp g st zp zl zc xp xl xc yp ylen yc mp n mc ret w0 len0 cap0 : Nat) (r29 : BitVec 64)
    (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 8) 1048 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 128)
    (hst1 : M.accessible st 24 false = true) (hst2 : st + 24 ≤ 2 ^ 48) (hstw : st + 24 ≤ sp - 8 ∨ sp + 1040 ≤ st)
    (hw0 : M.readLE st 8 = w0) (hl0 : M.readLE (st + 8) 8 = len0) (hc0 : M.readLE (st + 16) 8 = cap0)
    (hl16 : len0 ≤ 2 ^ 16) (hc40 : cap0 < 2 ^ 40) (hn : n ≤ 128) (hret48 : ret < 2 ^ 48)
    (hzp : zp < 2 ^ 64) (hzl : zl < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hyp : yp < 2 ^ 64) (hyl : ylen < 2 ^ 64) (hyc : yc < 2 ^ 64) (hmp : mp < 2 ^ 64)
    (hmc : mc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnE) (hsp : S.sp = BitVec.ofNat 64 (sp + 928))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 ylen)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h12 : S.regs 12 = BitVec.ofNat 64 mc) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (KJ : len0 + StackNat.rnd (23 * n) ≤ cap0 → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 enJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 xp → S'.regs 5 = BitVec.ofNat 64 xl →
      S'.regs 6 = BitVec.ofNat 64 xc → S'.regs 8 = BitVec.ofNat 64 ylen → S'.regs 10 = BitVec.ofNat 64 mp →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 13 = BitVec.ofNat 64 w0 → S'.regs 14 = BitVec.ofNat 64 len0 →
      S'.regs 15 = BitVec.ofNat 64 cap0 → S'.regs 9 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 1040)] → M'.regions = M.regions →
      ESl M' sp st r29 ret zp zc xp xl xc yp ylen mp n mc len0 →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q)
    (KG : cap0 < len0 + StackNat.rnd (23 * n) → ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 grE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 w0 → S'.regs 1 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) →
      S'.regs 2 = BitVec.ofNat 64 cap0 → S'.regs 3 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n) - cap0) →
      S'.regs 4 = BitVec.ofNat 64 wTy → S'.regs 30 = BitVec.ofNat 64 grRet →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 1040)] → M'.regions = M.regions →
      ESl M' sp st r29 ret zp zc xp xl xc yp ylen mp n mc len0 →
      M'.readLE (sp + 328) 8 = len0 + StackNat.rnd (23 * n) → M'.readLE (sp + 192) 8 = len0 →
      M'.readLE (sp + 216) 8 = len0 + StackNat.rnd (23 * n) - cap0 → M'.readLE (sp + 320) 8 = cap0 →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  generalize e18 : S.regs 18 = x18 at KJ KG
  have hr := rnd23 n hn
  have hm1 := mul23 n hn
  have hm2 := mul23' n hn
  have hrn : StackNat.rnd (23 * n) ≤ 23 * n + 3 := by simp only [StackNat.rnd]; omega
  have h63 : (BitVec.ofNat 64 (StackNat.rnd (23 * n))).getLsbD 63 = false :=
    getLsbD63_false _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  have e5 : BitVec.ofNat 64 len0 + BitVec.ofNat 64 (StackNat.rnd (23 * n)) =
      BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hti := toInt_sub3 len0 (StackNat.rnd (23 * n)) cap0 (by omega) (by omega) (by omega)
  rw [e5] at hti
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 928) - 928#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs8 : sp - 8 + 8 = sp := by omega
  have es2 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  by_cases hk : len0 + StackNat.rnd (23 * n) ≤ cap0
  · janus_run [es1, es2, hr, hm1, hm2, h63, e5, hti, hw0, hl0, hc0] until [enJ]
    refine KJ hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 1040)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    case sl =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := omega) only [hs8, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      all_goals first | omega | skip
    all_goals first | (janus_simp; done) | skip
  · have e3 : BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) - BitVec.ofNat 64 cap0 =
        BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n) - cap0) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have e1 : BitVec.ofNat 64 cap0 + BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n) - cap0) =
        BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    janus_run [es1, es2, hr, hm1, hm2, h63, e5, hti, e3, e1, hw0, hl0, hc0] until [grE]
    refine KG (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl ?q1 ?q2 ?q3 ?q4
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 1040)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    case sl =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := omega) only [hs8, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      all_goals first | omega | skip
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    all_goals omega

end FvModexp.Arm64.W4En
