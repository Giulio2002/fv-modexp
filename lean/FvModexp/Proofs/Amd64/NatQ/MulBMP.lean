import FvModexp.Proofs.Amd64.NatQ.MulCall
import FvModexp.Proofs.Amd64.Nat.BasicMul

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) — TIGHT COSTS] `nat.mul` (amd64), `2 ≤ n < 40`: `BasicMul.Pre` at the entry of `basicMul(z[0:m+n], x, y)` (entered at `RSP - 264`)

Small-context lemma (BRIEF speed lessons: stop at the callee entry, prove its pre separately); twin of
Amd64/NatQ/SqrBMP with two operands.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (inv_frame_win)

theorem apart_subL {a n m b k : Nat} (h : Apart a n b k) (hm : m ≤ n) : Apart a m b k := by
  unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bm_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st : Nat} {xp xl xc yp yl yc : BitVec 64}
    {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    {S1 : State} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg : S1.regs 14 = s.regs 14)
    (hfs : S1.fsBase = s.fsBase) (hF : MemFrame M S1.mem (win s W 88)) (hreg : S1.mem.regions = s.mem.regions) :
    BasicMul.Pre R b1 L1 (BitVec.ofNat 64 p) (BitVec.ofNat 64 (xl.toNat + yl.toNat)) (BitVec.ofNat 64 c) xp xl yp yl
      S1 := by
  have hce1 := hJ.callee (stk1 := 4224) (above1 := 72) hsp hg hfs hF hreg (by
    obtain ⟨-, hmw, -⟩ := hJ.pre; have := mulW64_ge xl.toNat yl.toNat; omega) (by omega)
  obtain ⟨hce, hmw, hsv, -, -, ⟨⟨hxlc, hxc40, hxl12, hxacc, hxh, hxw⟩, ⟨hylc, hyc40, hyl12, hyacc, hyh, hyw⟩, -, -⟩,
    -⟩ := hJ.pre
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, -, -, hout0, -⟩ := hce
  simp only [regSP] at hb0 ha0 hw0
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hpt := hJ.ptls (by omega)
  have hxw' := (hxw (by omega)).1
  have hyw' := (hyw (by omega)).1
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  obtain ⟨hyh', hy48⟩ := hyh (by omega)
  have hxacc' := hxacc (by omega)
  have hyacc' := hyacc (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hpw hxw' hyw'
  have hwin : ∀ a n, (a + n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 88 ≤ a) → Outside a n (win S1 4224 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hFs : MemFrame s.mem S1.mem (R.rt ++ win s W 88) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have tp : (BitVec.ofNat 64 p).toNat = p := IntAS.tN (by omega)
  have tc : (BitVec.ofNat 64 c).toNat = c := IntAS.tN (by omega)
  have t2 : (BitVec.ofNat 64 (xl.toNat + yl.toNat)).toNat = xl.toNat + yl.toNat := IntAS.tN (by omega)
  unfold BasicMul.Pre
  rw [tp, tc, t2]
  refine ⟨hce1, Nat.le_refl _, hcap, hc40, ?_, hwin _ _ (by omega), ?_, ?_, ?_, ?_, by omega, ?_, hwin _ _ (by omega),
    ?_, by omega, ?_, hwin _ _ (by omega), fun _ => ⟨?_, ?_, hsv.2.2.1 _ _ (by omega)⟩, ?_⟩
  · intro _; exact ⟨hp8, hph.sub (Nat.le_refl _) (by omega),
      by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega), by omega⟩
  · rw [hg]; exact apart_subL hpg (by omega)
  · rw [hfs]; exact apart_subL hpt (by omega)
  · rw [hF.accessible]; exact hJ.adx
  · rw [hFs.accessible]; exact hxacc'
  · exact hJ.ext.held (hxh'.sub (Nat.le_refl _) (by omega))
  · rw [hFs.accessible]; exact hyacc'
  · exact hJ.ext.held (hyh'.sub (Nat.le_refl _) (by omega))
  · exact apart_subL hpx (by omega)
  · exact apart_subL hpy (by omega)
  · rw [hg]; exact inv_frame_win hF hout0 (by omega) (by decide) hJ.inv

end FvModexp.Amd64.Q.NatMul
