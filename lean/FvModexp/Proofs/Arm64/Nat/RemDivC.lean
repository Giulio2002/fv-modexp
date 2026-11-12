import FvModexp.Proofs.Arm64.Nat.RemCall

set_option autoImplicit false

/-!
# `nat.rem` (arm64): from `stk.nat`'s return through `CALL nat.div` (`divc`)

`0x1b9104`: reload `stk`, `z`, `u`, `v` from the frame (`q` is in `X0..X2`), `CALL nat.div`; the precondition
(`ExpHyp.DivPre` at the return state `T` of `stk.nat`, same memory/`SP`/`g` as the call state) is a hypothesis.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatRem

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem divc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {cd : Nat → Nat → Nat → Nat} (hD : DHyp impl R cd) (b : Nat) (L : List (Nat × Nat)) (s T : State)
    (zp zl zc st up ul uc vp vl vc tq k : Nat) (ret : W64)
    (hb : zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ up < 2 ^ 64 ∧ ul < 2 ^ 64 ∧ uc < 2 ^ 64 ∧
      vp < 2 ^ 64 ∧ vl < 2 ^ 64 ∧ vc < 2 ^ 64 ∧ tq < 2 ^ 64 ∧ k < 2 ^ 64)
    (hpc : T.pc = BitVec.ofNat 64 (callNat + 4)) (hsp : T.sp = s.sp - 208#64) (h0s : 41712 ≤ s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (hw : T.mem.accessible (s.sp.toNat - 41712) (41712 + 112) true = true)
    (r0 : T.regs 0 = BitVec.ofNat 64 tq) (r1 : T.regs 1 = BitVec.ofNat 64 k) (r2 : T.regs 2 = BitVec.ofNat 64 k)
    (hsl : Sl s zp zl zc st up ul uc vp vl vc T.mem)
    (hpre : ∀ X : State, X.mem = T.mem → X.sp = T.sp → X.regs 28 = T.regs 28 →
      ExpHyp.DivPre R b cd L 41504 112 tq k k st zp zl zc up ul vp vl X) (Q : State → Prop)
    (kk : ∀ U X : State, X.mem = T.mem → X.sp = T.sp → X.regs 28 = T.regs 28 →
      U.pc = BitVec.ofNat 64 (callDiv + 4) → U.sp = T.sp → U.regs 28 = T.regs 28 → U.regs 29 = T.regs 29 →
      U.regs 18 = T.regs 18 → U.mem.regions = T.mem.regions →
      ExpHyp.DivPostL R b cd L 41504 112 tq k st zp zc up ul vp vl X U → ReachesRet (LibRem.program.link impl) ret U Q) :
    ReachesRet (LibRem.program.link impl) ret T Q := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
  have hspn : T.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  janus_run until [segAddr Extracted.program ExpHyp.fnDiv]
  refine ReachesRet.call_regions (dvsum impl hap R hD b L (BitVec.ofNat 64 tq) (BitVec.ofNat 64 k) (BitVec.ofNat 64 k)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 up)
    (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) (BitVec.ofNat 64 vp) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 vc)) rfl
    ⟨?ra, ?args, ?pre⟩ (fun U hU ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 (callDiv + 4) : BitVec 64).toNat = callDiv + 4 := by decide
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [e30]; exact raR impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom, setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    refine ⟨r0, r1, r2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [hsl.s3]
    · rw [hsl.zp']
    · rw [hsl.zl']
    · rw [hsl.zc']
    · rw [hsl.s4]
    · rw [hsl.s5]
    · rw [hsl.s6]
    · rw [hsl.s7]
    · rw [hsl.s8]
    · rw [hsl.s9]
  case pre =>
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3,
      Nat.mod_eq_of_lt b4, Nat.mod_eq_of_lt b5, Nat.mod_eq_of_lt b7, Nat.mod_eq_of_lt b8, Nat.mod_eq_of_lt b10,
      Nat.mod_eq_of_lt b11]
    exact hpre _ (by first | rfl | simp) (by first | rfl | exact hsp.symm) (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3,
    Nat.mod_eq_of_lt b4, Nat.mod_eq_of_lt b5, Nat.mod_eq_of_lt b7, Nat.mod_eq_of_lt b8, Nat.mod_eq_of_lt b10,
    Nat.mod_eq_of_lt b11, Nat.mod_eq_of_lt b6] at hq
  refine kk U _ (by first | rfl | simp) (by first | rfl | exact hsp.symm) (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by rw [hU]; simp only [setReg_apply, ↓reduceIte]) (by rw [f1]; exact hsp.symm) ?_ ?_ ?_ (by rw [hrg]) hq
  · rw [f2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · rw [f3]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · rw [f4]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]

end FvModexp.Arm64.NatRem
