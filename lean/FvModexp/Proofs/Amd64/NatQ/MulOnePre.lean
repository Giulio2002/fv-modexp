import FvModexp.Proofs.Amd64.NatQ.MulLift

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulOnePre.lean — TIGHT COSTS] `nat.mul` (amd64), `n = 1`: `mulAddWW`'s precondition at the call (`0x5f0bf3`, callee `RSP - 264`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (inv_frame_win tls)

theorem makeCost_need_le' {xl y : BitVec 64} (h : xl.toNat ≠ 0) :
    makeCost (MulAddWW.need xl y 0#64) ≤ makeB (xl.toNat + 1) := by
  unfold MulAddWW.need makeCost makeCap makeB allocCost
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true]
  split <;> (try split) <;> omega

theorem makeB_le_mulCQ1 {m : Nat} (h : m ≠ 0) : makeB (m + 1) ≤ mulCQ m 1 := by
  unfold mulCQ; rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]; exact MCQ_one

set_option maxRecDepth 20000 in
/-- **`MulAddWW.Pre` at `nat.mul`'s `n = 1` call** -/
theorem pre_one {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W : Nat} {zp zc xp xl : BitVec 64}
    {st xc yp yc : Nat} {y0 : BitVec 64} {s S1 : State}
    (hpre : MPre R b H L W zp.toNat zc.toNat st xp.toNat xl.toNat xc yp 1 yc s) (hx1 : xl.toNat ≠ 0)
    (hsp1 : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg1 : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hF1 : MemFrame s.mem S1.mem (win s W 88)) (hreg : S1.mem.regions = s.mem.regions) :
    MulAddWW.Pre R b L zp zc xp xl y0 0#64 S1 := by
  obtain ⟨hce, hmw, hsv, -, hty, hops, -, hcost, -, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  obtain ⟨⟨hxlc, -, hxl12, hxacc, hxh, hxw⟩, -, ⟨hzc40, hzl, hzw, hzs, hzx, -⟩, -⟩ := hops
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hF1' : MemFrame s.mem S1.mem (R.rt ++ win s W 88) := hF1.mono fun a n h => by
    simp only [outside_append] at h; exact h.2
  have hsub := win_sub (W := W) (ab := 88) (stk1 := 4208) (above1 := 72) hsp1 (by omega) (by omega) (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  have hmc : makeCost (MulAddWW.need xl y0 0#64) ≤ b := by
    have h1 := makeCost_need_le' (y := y0) hx1
    have h2 : makeB (xl.toNat + 1) ≤ mulCQ xl.toNat 1 := makeB_le_mulCQ1 hx1
    have := hcost.2; omega
  have hneed : MulAddWW.need xl y0 0#64 ≤ xl.toNat + 1 := by
    unfold MulAddWW.need; split <;> (try split) <;> simp_all
  refine ⟨callEnv_shift hce hLs hF1' hsp1 hg1 hfs hreg (by omega) (by omega) (by omega), hty,
    by omega, hzc40, ?_, hsub _ _ hzw, ?_, by rw [hF1.accessible]; exact hxacc (by omega), by omega,
    hxh'.sub (Nat.le_refl _) (by omega), hsub _ _ (hxw (by omega)).1, ?_, ?_⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF1.accessible]; exact a3, a4⟩
  · intro hc
    rw [hg1, hfs]
    refine ⟨(hzs hc).1, (hzs hc).2.1, ?_⟩
    rcases hzx with ⟨e1, -⟩ | h
    · exact Or.inl (BitVec.eq_of_toNat_eq e1)
    · exact Or.inr (h hc (by omega))
  · rw [hg1]; exact inv_frame_win hF1 hout (by omega) (by decide) hinv
  · intro _
    exact ⟨hsv.1 _ _ _ (by have := le_makeCap (MulAddWW.need xl y0 0#64); unfold makeCap at *; split <;> omega), hmc⟩

end FvModexp.Amd64.Q.NatMul
