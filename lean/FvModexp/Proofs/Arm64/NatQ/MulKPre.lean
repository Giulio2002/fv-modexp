import FvModexp.Proofs.Arm64.NatQ.MulCall
import FvModexp.Proofs.Arm64.NatQ.MulOps

/-!
# [Q-form copy of Arm64/Nat/MulKPre.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64): `KPre` at the call `karatsuba(stk, z[:2n], x[:n], y)` (`40 ≤ n ≤ m`), one frame down (`W - 256`)
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (StkPre StkSep stkOK_frame)

theorem StkPre.ext {R : RtInv} {L L1 : List (Nat × Nat)} {s : State} {W ab st : Nat} (h : StkPre R L s W ab st)
    (he : LiveExt R L L1) : StkPre R L1 s W ab st := by
  obtain ⟨h0, ⟨k1, k2, k3, k4, k5, k6, k7⟩, hstw, hstg, harr, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩ := h
  refine ⟨h0, ⟨k1, he.held k2, k3, k4, ?_, k6, k7⟩, hstw, hstg, harr, hfg, hfw, hsf, hswb, he.held hfh, hsgA, hfgA⟩
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
    {S1 : State} (hsp : S1.sp.toNat = s.sp.toNat - 256) (hg : S1.regs 28 = s.regs 28)
    (hF : MemFrame M S1.mem (winA s W 88)) (hreg : S1.mem.regions = s.mem.regions) :
    KPre R b1 H L1 (W - 256) st p (2 * yl) c xp yl xc yp yl yc S1 := by
  have hpre := hJ.pre
  obtain ⟨hce, hmw, hsv, hgl, hwt, hops, hstk, ⟨hlvH, hcost⟩, -⟩ := hpre
  obtain ⟨⟨hxlc, hxc40, hxl12, hxacc, hxh, hxw⟩, ⟨hylc, hyc40, hyl12, hyacc, hyh, hyw⟩, -, hlen⟩ := hops
  have hkw := kW_call h40 hyx
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hce' := hce
  obtain ⟨-, ⟨hal0, hb0, ha0, hw0⟩, -, hout0, -, -, hLs0, -⟩ := hce'
  have hFs : MemFrame s.mem S1.mem (R.rt ++ winA s W 88) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hLFs : LiveFrame s.mem S1.mem L [] :=
    LiveFrame.trans hJ.LF (lf_win' [] hF hLs0) fun _ _ h => h
  have hsub : ∀ a n, Outside a n (win s W 88) → Outside a n (win S1 (W - 256) 72) :=
    win_sub hsp (by omega) (by omega) hb0
  obtain ⟨eW, eL, eC⟩ := hdr_keep hstk.2.1 hstk.2.2.1 hFs hLFs
  have hfP : BasicSqr.freeP S1.mem st = BasicSqr.freeP s.mem st := by simp only [BasicSqr.freeP]; rw [eW, eL]
  have hfN : BasicSqr.freeN S1.mem st = BasicSqr.freeN s.mem st := by simp only [BasicSqr.freeN]; rw [eC, eL]
  have hcap := hJ.cap; have hc40 := hJ.c40
  obtain ⟨hp8, hph, hpacc, hp48⟩ := hJ.live (by omega)
  have hpw := hJ.pw
  have hpg := hJ.pg (by omega)
  have hpst := hJ.pst (by omega)
  have hpf := hJ.pfree (by omega)
  have hpgA := hJ.pgA (by omega)
  obtain ⟨hxw', hxs⟩ := hxw (by omega)
  obtain ⟨hyw', hys⟩ := hyw (by omega)
  obtain ⟨hxh', hx48⟩ := hxh (by omega)
  obtain ⟨hyh', hy48⟩ := hyh (by omega)
  have hb1 := kc_le h40 hyx hcost hJ.bud
  have hkw' : kW yl ≤ W - 256 := by have := Nat.le_trans hkw hmw; omega
  have hxw'' : Outside xp (8 * yl) (win s W 88) := hxw'.of_sub (Nat.le_refl _) (by omega)
  have hpx' : Apart p (8 * c) xp (8 * yl) := by unfold Apart at hpx ⊢; omega
  refine ⟨callEnv_shift hce hJ.lsep hFs hsp hg hreg (by omega) (by omega) (by omega) (by decide), hkw', hsv,
    globals_shift hgl hFs (fun a n h => winA_of_win' h) hsub, hwt, h40, rfl, rfl, by omega,
    ⟨⟨by omega, hxc40, by omega, fun _ => by rw [hFs.accessible]; exact Memory.accessible_mono _ (hxacc (by omega)) (Nat.le_refl _) (by omega),
      fun _ => ⟨hJ.ext.held hxh', hx48⟩, fun _ => ⟨hsub _ _ hxw'', ?_⟩⟩,
     ⟨hylc, hyc40, hyl12, fun h0 => by rw [hFs.accessible]; exact hyacc h0, fun _ => ⟨hJ.ext.held hyh', hy48⟩,
      fun _ => ⟨hsub _ _ hyw', ?_⟩⟩,
     ⟨hc40, fun _ => ⟨hp8, hph, by rw [hF.accessible]; exact hpacc, hp48⟩, hsub _ _ hpw,
      fun _ => ⟨by rw [hg]; exact hpg, ?_⟩,
      Or.inr fun _ _ => hpx',
      Or.inr fun _ _ => hpy⟩, by rw [eL]; omega⟩,
    hpx', hpy, hnx, hny,
    StkPre.ext (stkPre_shift hstk hFs hLFs hg hsub) hJ.ext, ⟨by rw [eL]; omega, by rw [stkR_congr eC]; exact hb1⟩, ?_⟩
  · show StkSep S1.mem st xp (8 * yl); simp only [StkSep, hfP, hfN]
    exact ⟨hxs.1.sub (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by omega),
      hxs.2.1.sub (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _),
      hxs.2.2.sub (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)⟩
  · show StkSep S1.mem st yp (8 * yl); simp only [StkSep, hfP, hfN]; exact hys
  · show StkSep S1.mem st p (8 * c); simp only [StkSep, hfP, hfN]
    exact ⟨by unfold Apart at hpst ⊢; omega, hpf, hpgA⟩
  · rw [hg]; exact inv_frame_winA hF hout0 (by omega) (by decide) hJ.inv

end FvModexp.Arm64.Q.NatMul
