import FvModexp.Proofs.Amd64.NatQ.MulCall
import FvModexp.Proofs.Amd64.NatQ.MulOps
import FvModexp.Proofs.Amd64.NatQ.SqrKPre

set_option autoImplicit false

/-!
# [amd64 port (divmc s44) of the Q-form Arm64/NatQ/MulKPre.lean — TIGHT COSTS] `nat.mul` (amd64): `KPre` at the call `karatsuba(stk, z[:2n], x[:n], y)` (`40 ≤ n ≤ m`), one frame down (callee `RSP - 264`, window `W - 264`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep stkOK_frame inv_frame_win globals_frame)

theorem StkPre.ext {R : RtInv} {L L1 : List (Nat × Nat)} {s : State} {W ab st : Nat} (h : StkPre R L s W ab st)
    (he : LiveExt R L L1) : StkPre R L1 s W ab st := by
  obtain ⟨h0, ⟨k1, k2, k3, k4, k5, k6, k7⟩, hstw, hstg, harr, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA, hsttl, hsatl,
    hftl⟩ := h
  refine ⟨h0, ⟨k1, he.held k2, k3, k4, ?_, k6, k7⟩, hstw, hstg, harr, hfg, hfw, hsf, hswb, he.held hfh, hsgA, hfgA,
    hsttl, hsatl, hftl⟩
  intro hc; obtain ⟨q1, q2, q3, q4⟩ := k5 hc; exact ⟨q1, he.held q2, q3, q4⟩

/-- the budget of `karatsuba(n)` fits in what `make` left (Q-form: the stack reserve `r` is carried along) -/
theorem kc_le {m n b b1 r : Nat} (h40 : 40 ≤ n) (hnm : n ≤ m) (hc : mulCQ m n + r ≤ b) (hb : b - makeB (m + n) ≤ b1) :
    KCQ n + r ≤ b1 := by
  unfold mulCQ at hc; rw [Nat.max_eq_left hnm, Nat.min_eq_right hnm] at hc
  rcases Nat.lt_or_ge n m with h | h
  · have := MCQ_loop h40 h; omega
  · have e : m = n := by omega
    subst e; have := MCQ_kar h40; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kpre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (hpx : Apart p (8 * c) xp (8 * xl))
    (hpy : Apart p (8 * c) yp (8 * yl)) (hnx : p + 8 * c ≠ xp + 8 * xc) (hny : p + 8 * c ≠ yp + 8 * yc)
    (h40 : 40 ≤ yl) (hyx : yl ≤ xl)
    {S1 : State} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg : S1.regs 14 = s.regs 14)
    (hfs : S1.fsBase = s.fsBase)
    (hF : MemFrame M S1.mem (win s W 88)) (hreg : S1.mem.regions = s.mem.regions) :
    KPre R b1 H L1 (W - 264) st p (2 * yl) c xp yl xc yp yl yc S1 := by
  have hpre := hJ.pre
  obtain ⟨hce, hmw, hsv, hgl, hwt, hops, hstk, ⟨hlvH, hcost⟩, -, -⟩ := hpre
  obtain ⟨⟨hxlc, hxc40, hxl12, hxacc, hxh, hxw⟩, ⟨hylc, hyc40, hyl12, hyacc, hyh, hyw⟩, -, hlen⟩ := hops
  have hkw := kW64_call h40 hyx
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hce' := hce
  obtain ⟨-, ⟨hb0, ha0, hw0⟩, hal0, -, hout0, -, -, hLs0, -⟩ := hce'
  simp only [regSP] at hb0 ha0 hw0
  have hFs : MemFrame s.mem S1.mem (R.rt ++ win s W 88) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hLFs : LiveFrame s.mem S1.mem L [] :=
    LiveFrame.trans hJ.LF (lf_win' [] hF hLs0) fun _ _ h => h
  have hsub : ∀ a n, Outside a n (win s W 88) → Outside a n (win S1 (W - 264) 72) :=
    win_sub hsp (by omega) (by omega) hb0
  obtain ⟨eW, eL, eC⟩ := hJ.hdrS hF
  have hfP : BasicSqr.freeP S1.mem st = BasicSqr.freeP s.mem st := by simp only [BasicSqr.freeP]; rw [eW, eL]
  have hfN : BasicSqr.freeN S1.mem st = BasicSqr.freeN s.mem st := by simp only [BasicSqr.freeN]; rw [eC, eL]
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hptl := hJ.ptls (by omega)
  have hpst := hJ.pst (by omega)
  have hpf := hJ.pfree (by omega)
  have hpgA := hJ.pgA (by omega)
  obtain ⟨hxw', hxs⟩ := hxw (by omega)
  obtain ⟨hyw', hys⟩ := hyw (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  obtain ⟨hyh', hy48⟩ := hyh (by omega)
  have hb1 := kc_le h40 hyx hcost hJ.bud
  have hkw' : kW64 yl ≤ W - 264 := by have := Nat.le_trans hkw hmw; omega
  have hxw'' : Outside xp (8 * yl) (win s W 88) := hxw'.of_sub (Nat.le_refl _) (by omega)
  have hpx' : Apart p (8 * c) xp (8 * yl) := by unfold Apart at hpx ⊢; omega
  have hgl' := hgl
  obtain ⟨-, -, -, -, -, -, -, -, -, hgw, -⟩ := hgl'
  have htd : NatSqr.tls S1 = NatSqr.tls s := by simp only [NatSqr.tls]; rw [hfs]
  refine ⟨hJ.callee (stk1 := W - 264) (above1 := 72) hsp hg hfs hF hreg (by omega) (by omega), hkw', hsv,
    globals_frame hgl hFs hgw hsub, hwt, h40, rfl, rfl, by omega,
    ⟨⟨by omega, hxc40, by omega,
      fun _ => by rw [hFs.accessible]; exact Arm64.Memory.accessible_mono _ (hxacc (by omega)) (Nat.le_refl _) (by omega),
      fun _ => ⟨hJ.ext.held hxh', hx48⟩, fun _ => ⟨hsub _ _ hxw'', ?_⟩⟩,
     ⟨hylc, hyc40, hyl12, fun h0 => by rw [hFs.accessible]; exact hyacc h0, fun _ => ⟨hJ.ext.held hyh', hy48⟩,
      fun _ => ⟨hsub _ _ hyw', ?_⟩⟩,
     ⟨hc40, fun _ => ⟨hp8, hph, by rw [hF.accessible]; exact hpacc, hp48⟩, hsub _ _ hpw,
      fun _ => ⟨by rw [hg]; exact hpg, by rw [htd]; exact hptl, ?_⟩,
      Or.inr fun _ _ => hpx',
      Or.inr fun _ _ => hpy⟩, by rw [eL]; omega⟩,
    hpx', hpy, hnx, hny,
    StkPre.ext (stkPre_shift hstk hFs hLFs hg hfs hsub) hJ.ext, ⟨by rw [eL]; omega, by rw [stkR_congr eC]; exact hb1⟩,
    by rw [hF.accessible]; exact hJ.adx, ?_⟩
  · show StkSep S1.mem st xp (8 * yl); simp only [StkSep, hfP, hfN]
    exact ⟨hxs.1.sub (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by omega),
      hxs.2.1.sub (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _),
      hxs.2.2.sub (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)⟩
  · show StkSep S1.mem st yp (8 * yl); simp only [StkSep, hfP, hfN]; exact hys
  · show StkSep S1.mem st p (8 * c); simp only [StkSep, hfP, hfN]
    exact ⟨by unfold Apart at hpst ⊢; omega, hpf, hpgA⟩
  · rw [hg]; exact inv_frame_win hF hout0 (by omega) (by decide) hJ.inv

end FvModexp.Amd64.Q.NatMul
