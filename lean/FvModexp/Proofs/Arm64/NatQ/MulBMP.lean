import FvModexp.Proofs.Arm64.NatQ.MulCall
import FvModexp.Proofs.Arm64.Nat.BasicMul
import FvModexp.Proofs.Arm64.Int.IntASCall

set_option autoImplicit false

/-!
# [TIGHT COSTS, divmc s48] `nat.mul` (arm64), `2 ≤ n < 40`: `BasicMul.Pre` at the entry of `basicMul(z[0:m+n], x, y)` (entered at `SP - 256`)

Small-context lemma (BRIEF speed lessons: stop at the callee entry, prove its pre separately); twin of the amd64
Amd64/NatQ/MulBMP. `mul_ra157`: the return address `0x1bb0e4` of the `BL basicMul` (`nat.mul` = `seg33`, base `0x1bae70`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

theorem apart_subL {a n m b k : Nat} (h : Apart a n b k) (hm : m ≤ n) : Apart a m b k := by
  unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
/-- the return address of `nat.mul`'s `BL basicMul` (`0x1bb0e0`) -/
theorem mul_ra157 {impl : List Segment} (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments BasicMul.names).link impl) 0x1bb0e4 := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg33)
    (show Extracted.seg33 ∈ Extracted.program.segments from
      List.getElem_mem (l := Extracted.program.segments) (n := 33) (by decide))
    (show BasicMul.names.contains Extracted.seg33.name = false by decide) 157
    (by simp [Extracted.seg33]) (by simp [Extracted.seg33]) (by decide)
  simpa [Extracted.seg33] using this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bm_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st : Nat} {xp xl xc yp yl yc : BitVec 64}
    {s : State} {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 M)
    (hpx : Apart p (8 * c) xp.toNat (8 * xl.toNat)) (hpy : Apart p (8 * c) yp.toNat (8 * yl.toNat))
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    {S1 : State} (hsp : S1.sp.toNat = s.sp.toNat - 256) (hg : S1.regs 28 = s.regs 28)
    (hF : MemFrame M S1.mem (winA s W 88)) (hreg : S1.mem.regions = s.mem.regions) :
    BasicMul.Pre R b1 L1 (BitVec.ofNat 64 p) (BitVec.ofNat 64 (xl.toNat + yl.toNat)) (BitVec.ofNat 64 c) xp xl yp yl
      S1 := by
  have hce1 := hJ.callee (stk1 := 4224) (above1 := 72) hsp hg hF hreg (by
    obtain ⟨-, hmw, -⟩ := hJ.pre; have := mulW_ge xl.toNat yl.toNat; omega) (by omega)
  obtain ⟨hce, hmw, hsv, -, -, ⟨⟨hxlc, hxc40, hxl12, hxacc, hxh, hxw⟩, ⟨hylc, hyc40, hyl12, hyacc, hyh, hyw⟩, -, -⟩,
    -⟩ := hJ.pre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, -, -⟩ := hce
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hxw' := (hxw (by omega)).1
  have hyw' := (hyw (by omega)).1
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  obtain ⟨hyh', hy48⟩ := hyh (by omega)
  have hxacc' := hxacc (by omega)
  have hyacc' := hyacc (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hpw hxw' hyw'
  have hwin : ∀ a n, (a + n ≤ s.sp.toNat - W ∨ s.sp.toNat + 88 ≤ a) → Outside a n (win S1 4224 72) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hFs : MemFrame s.mem S1.mem (R.rt ++ winA s W 88) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have tp : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have tc : (BitVec.ofNat 64 c).toNat = c := by simp only [BitVec.toNat_ofNat]; omega
  have t2 : (BitVec.ofNat 64 (xl.toNat + yl.toNat)).toNat = xl.toNat + yl.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  unfold BasicMul.Pre
  rw [tp, tc, t2]
  refine ⟨hce1, Nat.le_refl _, hcap, hc40, ?_, hwin _ _ (by omega), ?_, ?_, by omega, ?_, hwin _ _ (by omega),
    ?_, by omega, ?_, hwin _ _ (by omega), fun _ => ⟨?_, ?_, hsv.2.2.1 _ _ (by omega)⟩, ?_⟩
  · intro _; exact ⟨hp8, hph.sub (Nat.le_refl _) (by omega),
      by rw [hF.accessible]; exact Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega), by omega⟩
  · rw [hg]; exact apart_subL hpg (by omega)
  · rw [hFs.accessible]; exact hxacc'
  · exact hJ.ext.held (hxh'.sub (Nat.le_refl _) (by omega))
  · rw [hFs.accessible]; exact hyacc'
  · exact hJ.ext.held (hyh'.sub (Nat.le_refl _) (by omega))
  · exact apart_subL hpx (by omega)
  · exact apart_subL hpy (by omega)
  · rw [hg]; exact inv_frame_winA hF hout0 (by omega) (by decide) hJ.inv

end FvModexp.Arm64.Q.NatMul
