import FvModexp.Proofs.Amd64.Exp.W2EnDefs

set_option autoImplicit false

/-!
# window-2 entry (amd64): entry → the `slices.Grow` decision (fn+0x0 .. fn+0x140) (agent expmc s63; ported from
`Amd64.W4EnA`)

`enA`: stack-guard check, prologue, spills, defer record, `nr = rnd(11n)`; then either the join `enJ` (`len + nr ≤ cap`,
no growth) or the entry of `growslice(w, len + nr, cap, len + nr - cap, Word)` (return `grRet`). Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2En

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enA {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp g st zp zl zc xp xl xc yp ylen mp n mc bp r w0 len0 cap0 : Nat} {M : Memory}
    (hal : sp % 8 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x2e0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 8) 0x2e8 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 0x60)
    (hst1 : M.accessible st 24 false = true) (hst2 : st + 24 ≤ 2 ^ 48) (hstw : st + 24 ≤ sp ∨ sp + 0x2e0 ≤ st)
    (hw0 : M.readLE st 8 = w0) (hl0 : M.readLE (st + 8) 8 = len0) (hc0 : M.readLE (st + 16) 8 = cap0)
    (hl16 : len0 ≤ 2 ^ 16) (hc40 : cap0 < 2 ^ 40) (hlc : len0 ≤ cap0) (hn : n ≤ 128)
    (hzp : zp < 2 ^ 64) (hzl : zl < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hbp : bp < 2 ^ 64)
    (r388 : M.readLE (sp + 0x270) 8 = r) (r390 : M.readLE (sp + 0x278) 8 = yp) (r398 : M.readLE (sp + 0x280) 8 = ylen)
    (r3a8 : M.readLE (sp + 0x290) 8 = mp) (r3b0 : M.readLE (sp + 0x298) 8 = n) (r3b8 : M.readLE (sp + 0x2a0) 8 = mc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x270)) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h5 : S.regs 5 = BitVec.ofNat 64 bp) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hx15 : S.xmm 15 = 0)
    (KJ : len0 + StackNat.rnd (11 * n) ≤ cap0 → ∀ (S' : State) (M' : Memory),
      S'.rip = BitVec.ofNat 64 enJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = BitVec.ofNat 64 (sp + 0x268) →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 6 = BitVec.ofNat 64 xp → S'.regs 8 = BitVec.ofNat 64 xl →
      S'.regs 9 = BitVec.ofNat 64 xc → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 13 = BitVec.ofNat 64 len0 →
      S'.regs 15 = BitVec.ofNat 64 cap0 → S'.regs 2 = BitVec.ofNat 64 (StackNat.rnd (11 * n)) →
      S'.regs 10 = BitVec.ofNat 64 (5 * n) →
      S'.regs 11 = BitVec.ofNat 64 w0 → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase = S.fsBase → S'.xmm 15 = 0 → S'.df = S.df →
      S'.mem = M' → MemFrame M M' [(sp, sp + 0x270), (sp + 0x2a8, sp + 0x2e0)] → M'.regions = M.regions →
      ESl M' sp st bp r zp zc xp xl xc yp ylen mp n mc len0 → M'.readLE (sp + 0x148) 8 = 5 * n →
      ReachesRet (LibW.program.link impl) ret S' Q)
    (KG : cap0 < len0 + StackNat.rnd (11 * n) → ∀ (S' : State) (M' : Memory),
      S'.rip = BitVec.ofNat 64 grE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 5 = BitVec.ofNat 64 (sp + 0x268) →
      S'.regs 0 = BitVec.ofNat 64 w0 → S'.regs 3 = BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n)) →
      S'.regs 1 = BitVec.ofNat 64 cap0 → S'.regs 7 = BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n) - cap0) →
      S'.regs 6 = BitVec.ofNat 64 wTy → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase = S.fsBase → S'.xmm 15 = 0 → S'.df = S.df →
      S'.mem = M' → MemFrame M M' [(sp - 8, sp + 0x270), (sp + 0x2a8, sp + 0x2e0)] → M'.regions = M.regions →
      ESl M' sp st bp r zp zc xp xl xc yp ylen mp n mc len0 → M'.readLE (sp + 0x148) 8 = 5 * n →
      M'.readLE (sp - 8) 8 = grRet →
      M'.readLE (sp + 0x140) 8 = StackNat.rnd (11 * n) → M'.readLE (sp + 0xb8) 8 = len0 →
      M'.readLE (sp + 0xd0) 8 = len0 + StackNat.rnd (11 * n) - cap0 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have h5n := e5n n hn
  have h11n := e11n n hn
  have hr := rnd11 n hn
  have hrn := rnd23_le n
  have hti := StackNat.toInt_sub3' len0 (StackNat.rnd (11 * n)) cap0 (by omega) (by omega) (by omega) hlc
  have hgs : S.mem.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hs8 : sp + 0x270 - 8 = sp + 0x268 := by omega
  have e5 : BitVec.ofNat 64 (sp + 0x270) - 8#64 = BitVec.ofNat 64 (sp + 0x268) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e6 : BitVec.ofNat 64 (sp + 0x268) - 0x268#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmsb : (BitVec.ofNat 64 (StackNat.rnd (11 * n))).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp only [decide_eq_false_iff_not]; omega
  have hms := sub3_msb len0 (StackNat.rnd (11 * n)) cap0 (by omega) (by omega) (by omega) hlc
  have hzs := sub3_z len0 (StackNat.rnd (11 * n)) cap0 (by omega) (by omega) (by omega) hlc
  by_cases hk : len0 + StackNat.rnd (11 * n) ≤ cap0
  · have hc3 : len0 + StackNat.rnd (11 * n) < cap0 ∨ len0 + StackNat.rnd (11 * n) = cap0 := by omega
    rcases hc3 with hc3 | hc3
    · have hms' : (BitVec.ofNat 64 (StackNat.rnd (11 * n)) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0)).msb =
          true := by rw [hms]; simp only [decide_eq_true_eq]; exact hc3
      have hzs' := hzs.trans (show (len0 + StackNat.rnd (11 * n) = cap0) = False by
        simp only [eq_iff_iff, iff_false]; omega)
      janus64_run [h5n, h11n, hr, hw0, hl0, hc0, r3b0, e5, e6, hmsb, hms', hzs'] until [enJ]
      refine KJ hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl ?q148
      case mf => janus_frame
      case q148 =>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      case sl =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        all_goals first | omega | exact r388 | exact r390 | exact r398 | exact r3a8 | exact r3b0 | exact r3b8 | skip
      all_goals first | (janus64_simp; done) | skip
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals first | exact h7 | exact h6 | exact h8 | exact h9 | exact h14 | rfl
    · have hms' : (BitVec.ofNat 64 (StackNat.rnd (11 * n)) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0)).msb =
          false := by rw [hms]; simp only [decide_eq_false_iff_not]; omega
      have hzs' := hzs.trans (show (len0 + StackNat.rnd (11 * n) = cap0) = True by simp only [eq_iff_iff, iff_true]; omega)
      janus64_run [h5n, h11n, hr, hw0, hl0, hc0, r3b0, e5, e6, hmsb, hms', hzs'] until [enJ]
      refine KJ hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl ?q148
      case mf => janus_frame
      case q148 =>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      case sl =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        all_goals first | omega | exact r388 | exact r390 | exact r398 | exact r3a8 | exact r3b0 | exact r3b8 | skip
      all_goals first | (janus64_simp; done) | skip
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals first | exact h7 | exact h6 | exact h8 | exact h9 | exact h14 | rfl
  · have hms' : (BitVec.ofNat 64 (StackNat.rnd (11 * n)) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0)).msb =
        false := by rw [hms]; simp only [decide_eq_false_iff_not]; omega
    have hzs' := hzs.trans (show (len0 + StackNat.rnd (11 * n) = cap0) = False by simp only [eq_iff_iff, iff_false]; omega)
    have e9 : BitVec.ofNat 64 (StackNat.rnd (11 * n)) - (BitVec.ofNat 64 cap0 - BitVec.ofNat 64 len0) =
        BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n) - cap0) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have e10 : BitVec.ofNat 64 cap0 + BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n) - cap0) =
        BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hlt : BitVec.ofNat 64 cap0 ≤ BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n)) := by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
    have hlt' : ¬ BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n)) ≤ BitVec.ofNat 64 cap0 := by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
    have hm9 : (BitVec.ofNat 64 (len0 + StackNat.rnd (11 * n) - cap0)).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp only [decide_eq_false_iff_not]
      omega
    have hz9 : ((len0 + StackNat.rnd (11 * n) - cap0) % 18446744073709551616 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have hz9' : (len0 + StackNat.rnd (11 * n) - cap0 = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    janus64_run [h5n, h11n, hr, hw0, hl0, hc0, r3b0, e5, e6, hmsb, hms', hzs', e9, e10, hlt, hlt', hm9, hz9, hz9'] until [grE]
    refine KG (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?sl ?q148 ?q0 ?q1 ?q2 ?q3
    case mf => janus_frame
    case sl =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      all_goals first | omega | exact r388 | exact r390 | exact r398 | exact r3a8 | exact r3b0 | exact r3b8 | skip
    all_goals first | (janus64_simp; done) | skip
    all_goals simp (disch := omega) only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    all_goals first | exact h14 | rfl | omega |
      (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.W2En
