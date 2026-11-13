import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsFRel

/-! (Q-form copy of Arm64/Nat/DrsFRecP.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block: the precondition of the recursive call (pure)

`rec_preF`: at the call `qhat.divRecursiveStep(stk, u[s:].norm(), v[s:], depth+1)` (natdiv.go:863; call state `X`,
`SP = entry SP - 400`): `DrsPreW` of the callee with window `W - 400`, arguments `z = qhat0 (B+1, B+1)`,
`u = u[B-1 : B-1+k] (cap uc-(B-1))` (`k` = the normalised length), `v = v[B-1:] (n-B+1, cap vc-(B-1))`; the
dividend bound `hval` is supplied by the caller (from the loop invariant). Adapted from `rec_pre` (DrsRecP).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 16000000 in
theorem rec_preF {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk k : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s))
    (hvk : X.mem.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)) (hk : k ≤ c.u1 - (c.vl / 2 - 1))
    (hval : 2 * natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) k < 2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))))
    (hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0)
    (hsp : X.sp.toNat = s.sp.toNat - 400) (h28 : X.regs 28 = s.regs 28)
    (hbud : drsCQ c.ul (c.vl - c.vl / 2 + 1) + stkR c.Hq X.mem c.st ≤ bk) :
    DrsPreW R bk Lk c.Hq (drsCQ k (c.vl - c.vl / 2 + 1)) (c.W - 400) c.t0 (c.vl / 2 + 1)
      (c.vl / 2 + 1) c.st (c.up + 8 * (c.vl / 2 - 1)) k (c.uc - (c.vl / 2 - 1)) (c.vp + 8 * (c.vl / 2 - 1))
      (c.vl - c.vl / 2 + 1) (c.vc - (c.vl / 2 - 1)) X := by
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, hsv, hgl, -, -, hulc, huc, hvlc, hvc, -, ⟨hvl9, -⟩, htop, -, -,
    ⟨-, -, -, -, -⟩, ⟨hua, hu48, huh, huo, hug⟩, ⟨hva, hv48, hvh, hvo, hvgA, hvch, hvc48⟩, -, -, huv,
    ⟨-, hstw, hstg, harr⟩, ⟨hstl, -, hvcf, hst0⟩, -, ⟨hus, -⟩, ⟨hvs, -⟩, hswb, -, -, ⟨hq, hugA, hstgA, hfg⟩, hcq, -⟩ := hcr.pre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', -, hw⟩, -, hout, hga, hgr, -, -⟩ := hce'
  have hlen := hfp.len
  have hok := hev.sok
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hok.2.2.2.2.2.1
  have hwin : ∀ a n, Outside a n (win s c.W 96) → Outside a n (win X (c.W - 400) 96) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hev.fr.accessible a n w
  -- the globals
  have hglX : RunIface.Globals R X.mem (win X (c.W - 400) 96) := by
    obtain ⟨g1, g2, g3, g4, e1, e2, e3, g5, g6, g7, g8, g9, g10⟩ := hgl
    have egA : RunIface.gA = Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» := rfl
    have rg : ∀ x n, RunIface.gA ≤ x → x + n ≤ RunIface.gA + 32 → X.mem.readLE x n = s.mem.readLE x n := by
      intro x n h1 h2
      refine hev.fr.readLE _ _ ?_
      unfold Apart at hq hugA hstgA hfg
      simp only [win, winA, Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at g7 ⊢
      have g6' := g6.of_sub h1 h2
      and_intros <;> first | exact g6' | omega
    refine ⟨by rw [rg _ _ (by omega) (by omega)]; exact g1, by rw [rg _ _ (by omega) (by omega)]; exact g2,
      by rw [rg _ _ (by omega) (by omega)]; exact g3, by rw [rg _ _ (by omega) (by omega)]; exact g4, e1, e2, e3,
      by rw [hacc]; exact g5, g6, hwin _ _ g7, by rw [hacc]; exact g8, g9, ?_⟩
    simp only [win, outside_cons, outside_nil, and_true] at g10 ⊢; rw [hsp]; omega
  -- the stack's array
  have hstin : EvenHyp.StkIn R Lk X (c.W - 400) 96 c.st := by
    refine ⟨hok, hwin _ _ hstw, by rw [h28]; exact hstg, fun hc => ?_⟩
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · simp only [e1, e2] at hc ⊢; obtain ⟨a1, a2⟩ := harr hc; exact ⟨hwin _ _ a1, by rw [h28]; exact a2⟩
    · have h1 := FvModexp.Arm64.NatAdd.outside_of_inRanges hout hin
      have h2 := FvModexp.Arm64.NatAdd.outside_of_inRanges hgr hin
      refine ⟨?_, ?_⟩
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · rw [h28]; unfold Apart; omega
  -- v top
  have htopX : 2 ^ 63 ≤ X.mem.readLE (c.vp + 8 * (c.vl / 2 - 1) + 8 * (c.vl - c.vl / 2 + 1 - 1)) 8 := by
    rw [show c.vp + 8 * (c.vl / 2 - 1) + 8 * (c.vl - c.vl / 2 + 1 - 1) = c.vp + 8 * (c.vl - 1) by omega,
      rd_sub hvk (by omega) (by omega)]; exact htop
  have t0s := hcr.t0st; have t0u := hcr.t0u; have t0v := hcr.t0v; have t0g := hcr.t0g; have t0gA := hcr.t0gA
  have fq := hfp.ft0; have fu := hfp.fu; have fv := hfp.fv; have fst := hfp.fst; have fgA := hfp.fgA
  rw [← hlen] at fq fu fv fst fgA
  have hvcX : Apart c.vp (8 * c.vc) (stW X.mem c.st + 8 * stLen X.mem c.st)
      (8 * (stCap X.mem c.st - stLen X.mem c.st)) := by
    have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
    rcases free_loc hev hl with ⟨h1, h2⟩ | ⟨hin, hap⟩
    · unfold Apart at hvcf ⊢; omega
    · exact fresh_apart hvch hin hap
  have hlB : stLen X.mem c.st + 12 * (c.vl - c.vl / 2 + 1) + 64 ≤ 2 ^ 16 := by
    rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega
  refine ⟨Ev.callEnv hcr hev hsp h28 (by omega) (by omega), hsv, hglX, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ⟨by omega, by omega⟩, htopX, by simp only [natVal]; exact hq0, hval,
    ⟨by rw [hacc]; exact hcr.t0acc, hcr.t048, hev.ext.held hcr.t0h, hwin _ _ hcr.t0w, by rw [h28]; exact t0g⟩,
    ⟨by rw [hacc]; exact Memory.accessible_mono _ hua (by omega) (by omega), by omega,
      hext.held (huh.sub (by omega) (by omega)), hwin _ _ (huo.of_sub (by omega) (by omega)),
      by rw [h28]; exact apL hug (by omega) (by omega)⟩,
    ⟨by rw [hacc]; exact Memory.accessible_mono _ hva (by omega) (by omega), by omega,
      hext.held (hvh.sub (by omega) (by omega)), hwin _ _ (hvo.of_sub (by omega) (by omega)),
      apL hvgA (by omega) (by omega), hext.held (hvch.sub (by omega) (by omega)), by omega⟩,
    apR t0u (by omega) (by omega), apR t0v (by omega) (by omega), apR (apL huv (by omega) (by omega)) (by omega) (by omega),
    hstin, ⟨hlB, by rw [hlen] at hlc; simp only [Cx.l1, StackNat.rnd] at hlc; omega, apL hvcX (by omega) (by omega),
      ⟨hst0.1, by have := hst0.2.1; omega, hcr.t0al⟩⟩, ⟨t0s, fq.symm⟩, ⟨apL hus (by omega) (by omega), apL fu.symm (by omega) (by omega)⟩,
    ⟨apL hvs (by omega) (by omega), apL fv.symm (by omega) (by omega)⟩, hswb, fst,
    by rw [hlen]; exact hwin _ _ hfp.fw, ⟨t0gA, apL hugA (by omega) (by omega), hstgA, fgA⟩, ?_, by rw [h28]; exact hev.inv⟩
  refine ⟨by rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega,
    Nat.le_trans (Nat.add_le_add_right (drsCQ_ul _ _ _ (by omega)) _) hbud⟩

end FvModexp.Arm64.Q.DivRec
