import FvModexp.Proofs.Amd64.NatQ.SqrCall

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/SqrBMP.lean — TIGHT COSTS, divmc s38] `nat.sqr` (amd64), `2 ≤ n < 12`: `BasicMul.Pre` at the entry of `basicMul(z[0:2n], x, x)` (entered at `RSP - 176`)

Small-context lemma (BRIEF speed lessons: stop at the callee entry, prove its pre separately).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bm_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp xl xc s p c L1 b1 M) (hpx : Apart p (8 * c) xp (8 * xl)) (hx2 : 2 ≤ xl)
    {S1 : State} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 176) (hg : S1.regs 14 = s.regs 14)
    (hfs : S1.fsBase = s.fsBase) (hF : MemFrame M S1.mem (win s W 64)) (hreg : S1.mem.regions = s.mem.regions) :
    BasicMul.Pre R b1 L1 (BitVec.ofNat 64 p) (BitVec.ofNat 64 (2 * xl)) (BitVec.ofNat 64 c) (BitVec.ofNat 64 xp)
      (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) S1 := by
  have hce1 := hJ.callee (stk1 := 4224) (above1 := 72) hsp hg hfs hF hreg (by
    obtain ⟨-, hsw, -⟩ := hJ.pre; unfold sqrW ksqrW at hsw; omega) (by omega)
  obtain ⟨hce, hsw, hsv, -, -, hxlc, hxc40, hxl12, hxacc, hxh, hxw, -⟩ := hJ.pre
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, -, -, hout0, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hpt := hJ.ptls (by omega)
  have hxw' := hxw (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hpw hxw'
  have hwin : ∀ a n, (a + n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 64 ≤ a) → Outside a n (win S1 4224 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hFs : MemFrame s.mem S1.mem (R.rt ++ win s W 64) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have tp : (BitVec.ofNat 64 p).toNat = p := IntAS.tN (by omega)
  have tc : (BitVec.ofNat 64 c).toNat = c := IntAS.tN (by omega)
  have tx : (BitVec.ofNat 64 xp).toNat = xp := IntAS.tN (by omega)
  have tl : (BitVec.ofNat 64 xl).toNat = xl := IntAS.tN (by omega)
  have t2 : (BitVec.ofNat 64 (2 * xl)).toNat = 2 * xl := IntAS.tN (by omega)
  unfold BasicMul.Pre
  rw [tp, tc, tx, tl, t2]
  refine ⟨hce1, by omega, hcap, hc40, ?_, hwin _ _ (by omega), ?_, ?_, ?_, ?_, by omega, ?_, hwin _ _ (by omega), ?_,
    by omega, ?_, hwin _ _ (by omega), fun _ => ⟨?_, ?_, hsv.2.2.1 _ _ (by omega)⟩, ?_⟩
  · intro _; exact ⟨hp8, hph.sub (Nat.le_refl _) (by omega),
      by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega), by omega⟩
  · rw [hg]; exact Apart.subL hpg (by omega)
  · rw [hfs]; exact Apart.subL hpt (by omega)
  · rw [hF.accessible]; exact hJ.adx
  · rw [hFs.accessible]; exact hxacc
  · exact hJ.ext.held (hxh'.sub (Nat.le_refl _) (by omega))
  · rw [hFs.accessible]; exact hxacc
  · exact hJ.ext.held (hxh'.sub (Nat.le_refl _) (by omega))
  · exact Apart.subL hpx (by omega)
  · exact Apart.subL hpx (by omega)
  · rw [hg]; exact inv_frame_win hF hout0 (by omega) (by decide) hJ.inv

end FvModexp.Amd64.Q.NatSqr
