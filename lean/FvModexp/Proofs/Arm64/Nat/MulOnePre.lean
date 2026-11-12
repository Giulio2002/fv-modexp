import FvModexp.Proofs.Arm64.Nat.MulLift
import FvModexp.Proofs.Arm64.Nat.MulAddWWX

/-!
# `nat.mul` (arm64), `n = 1`: `mulAddWW`'s precondition at the call (`0x1bb108`, callee `SP - 256`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

theorem makeCost_need_le' {xl y : BitVec 64} (h : xl.toNat ≠ 0) :
    makeCost (MulAddWW.need xl y 0#64) ≤ makeB (xl.toNat + 1) := by
  unfold MulAddWW.need makeCost makeCap makeB allocCost
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true]
  split <;> (try split) <;> omega

theorem makeB_le_mulC1 {ℓ m : Nat} (h : m ≠ 0) : makeB (m + 1) ≤ mulC ℓ m 1 := by
  unfold mulC; rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]; exact MC_one

/-- `nat.mul`'s window (`SP - W … SP + 88`) contains the `n = 1` callee's (`SP - 256 - 4208 … SP - 184`) -/
theorem wsub_one {s S1 : State} {W : Nat} (hsp1 : S1.sp.toNat = s.sp.toNat - 256) (hW : 4608 ≤ W)
    (hb : W ≤ s.sp.toNat) : ∀ a n, Outside a n (winA s W 88) → Outside a n (winA S1 4208 72) := by
  intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp1]; omega

set_option maxRecDepth 20000 in
/-- **`MulAddWW.Pre` at `nat.mul`'s `n = 1` call** -/
theorem pre_one {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W : Nat} {zp zc xp xl : BitVec 64}
    {st xc yp yc : Nat} {y0 : BitVec 64} {s S1 : State}
    (hpre : MPre R b L W zp.toNat zc.toNat st xp.toNat xl.toNat xc yp 1 yc s) (hx1 : xl.toNat ≠ 0)
    (hsp1 : S1.sp.toNat = s.sp.toNat - 256) (hg1 : S1.regs 28 = s.regs 28)
    (hF1 : MemFrame s.mem S1.mem (winA s W 88)) (hreg : S1.mem.regions = s.mem.regions) :
    MulAddWW.Pre R b L zp zc xp xl y0 0#64 S1 := by
  obtain ⟨hce, hmw, hsv, -, hty, hops, -, hcost, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce'
  obtain ⟨⟨hxlc, -, hxl12, hxacc, hxh, hxw⟩, -, ⟨hzc40, hzl, hzw, hzs, hzx, -⟩, -⟩ := hops
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hF1' : MemFrame s.mem S1.mem (R.rt ++ winA s W 88) := hF1.mono fun a n h => by
    simp only [outside_append] at h; exact h.2
  have hsub := win_sub (W := W) (ab := 88) (stk1 := 4208) (above1 := 72) hsp1 (by omega) (by omega) (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  have hneed : MulAddWW.need xl y0 0#64 ≤ xl.toNat + 1 := by
    unfold MulAddWW.need; split <;> (try split) <;> simp_all
  have hmc : makeCost (MulAddWW.need xl y0 0#64) ≤ b := by
    have h1 := makeCost_need_le' (y := y0) hx1
    have h2 : makeB (xl.toNat + 1) ≤ mulC (stLen s.mem st) xl.toNat 1 := makeB_le_mulC1 hx1
    omega
  refine ⟨callEnv_shift hce hLs hF1' hsp1 hg1 hreg (by omega) (by omega) (by omega) (by omega), hty,
    by omega, hzc40, ?_, hsub _ _ hzw, ?_, by rw [hF1.accessible]; exact hxacc, by omega,
    hxh'.sub (Nat.le_refl _) (by omega), hsub _ _ (hxw (by omega)).1, ?_, ?_⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF1.accessible]; exact a3, a4⟩
  · intro hc
    rw [hg1]
    refine ⟨(hzs hc).1, ?_⟩
    rcases hzx with ⟨e1, -⟩ | h
    · exact Or.inl (BitVec.eq_of_toNat_eq e1)
    · exact Or.inr (h hc (by omega))
  · rw [hg1]; exact inv_frame_winA hF1 hout (by omega) (by decide) hinv
  · intro _
    exact ⟨hsv.1 _ _ _ (by have := le_makeCap (MulAddWW.need xl y0 0#64); unfold makeCap at *; split <;> omega), hmc⟩

end FvModexp.Arm64.NatMul
