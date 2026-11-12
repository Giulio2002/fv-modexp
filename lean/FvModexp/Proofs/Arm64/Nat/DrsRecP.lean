import FvModexp.Proofs.Arm64.Nat.DrsEnv

/-!
# `divRecursiveStep` (arm64), loop body: the precondition of the recursive call (pure)

`rec_pre`: at the call `qhat.divRecursiveStep(stk, uu[s:B+n], v[s:], depth+1)` (natdiv.go:813; call state `X`,
`SP = entry SP - 400`): `DrsPreW` of the callee with window `W - 400`, live set `Lk`, budget `bk`, arguments
`z = qhat0 (B+1, B+1)`, `u = u[j-1 : j+n] (cap uc-(j-1))`, `v = v[B-1:] (n-B+1, cap vc-(B-1))`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

theorem apL {a n b k a' n' : Nat} (h : Apart a n b k) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Apart a' n' b k := by
  unfold Apart at h ⊢; omega

theorem apR {a n b k b' k' : Nat} (h : Apart a n b k) (h1 : b ≤ b') (h2 : b' + k' ≤ b + k) : Apart a n b' k' := by
  unfold Apart at h ⊢; omega

set_option maxHeartbeats 16000000 in
theorem rec_pre {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk j : Nat} {Z : List Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s)) (hbd : Bd c s X.mem j Z)
    (hj : c.vl / 2 < j) (hjm : j ≤ c.u1 - c.vl) (hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0)
    (hsp : X.sp.toNat = s.sp.toNat - 400) (h28 : X.regs 28 = s.regs 28)
    (hbud : drsC (c.l1 s) c.ul (c.vl - c.vl / 2 + 1) ≤ bk) :
    DrsPreW R bk Lk (drsC (stLen X.mem c.st) (c.vl + 1) (c.vl - c.vl / 2 + 1)) (c.W - 400) c.t0 (c.vl / 2 + 1)
      (c.vl / 2 + 1) c.st (c.up + 8 * (j - 1)) (c.vl + 1) (c.uc - (j - 1)) (c.vp + 8 * (c.vl / 2 - 1))
      (c.vl - c.vl / 2 + 1) (c.vc - (c.vl / 2 - 1)) X := by
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, hsv, hgl, -, -, hulc, huc, hvlc, hvc, -, ⟨hvl9, -⟩, htop, -, -,
    ⟨-, -, -, -, -⟩, ⟨hua, hu48, huh, huo, hug⟩, ⟨hva, hv48, hvh, hvo, hvgA, hvch, hvc48⟩, -, -, huv,
    ⟨-, hstw, hstg, harr⟩, ⟨hstl, -⟩, -, ⟨hus, -⟩, ⟨hvs, -⟩, hswb, -, -, ⟨hq, hugA, hstgA, hfg⟩, -, -⟩ := hcr.pre
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
      rd_sub hbd.vk (by omega) (by omega)]; exact htop
  have hval : 2 * natVal X.mem (c.up + 8 * (j - 1)) (c.vl + 1) <
      2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) := by
    have h1 := natVal_lt X.mem (c.up + 8 * (j - 1)) (c.vl + 1)
    have e : 64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1)) = 64 * (c.vl + 1) + 1 + 63 := by omega
    rw [e, Nat.pow_add, Nat.pow_add]
    have : 1 ≤ 2 ^ 63 := Nat.one_le_two_pow
    have : 2 * natVal X.mem (c.up + 8 * (j - 1)) (c.vl + 1) < 2 ^ (64 * (c.vl + 1)) * 2 ^ 1 := by omega
    exact Nat.lt_of_lt_of_le this (Nat.le_mul_of_pos_right _ (by omega))
  have t0s := hcr.t0st; have t0u := hcr.t0u; have t0v := hcr.t0v; have t0g := hcr.t0g; have t0gA := hcr.t0gA
  have fq := hfp.ft0; have fu := hfp.fu; have fv := hfp.fv; have fst := hfp.fst; have fgA := hfp.fgA
  rw [← hlen] at fq fu fv fst fgA
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
    hstin, ⟨hlB, by rw [hlen] at hlc; simp only [Cx.l1, StackNat.rnd] at hlc; omega⟩, ⟨t0s, fq.symm⟩, ⟨apL hus (by omega) (by omega), apL fu.symm (by omega) (by omega)⟩,
    ⟨apL hvs (by omega) (by omega), apL fv.symm (by omega) (by omega)⟩, hswb, fst,
    by rw [hlen]; exact hwin _ _ hfp.fw, ⟨t0gA, apL hugA (by omega) (by omega), hstgA, fgA⟩, ?_, by rw [h28]; exact hev.inv⟩
  rw [hlen]; exact Nat.le_trans (drsC_ul _ _ _ _ (by omega)) hbud

end FvModexp.Arm64.DivRec
