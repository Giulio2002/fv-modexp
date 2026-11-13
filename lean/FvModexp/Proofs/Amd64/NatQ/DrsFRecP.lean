import FvModexp.Proofs.Amd64.NatQ.DrsFRel

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsFRecP.lean; adapted from Amd64/NatQ/DrsRecP.lean)
# `divRecursiveStep` (amd64), final block: the precondition of the recursive call (no janus runs)

`rec_preF`: at the callee entry `X` (`RSP = r - 400`) of `qhat.divRecursiveStep(stk, u[s:].norm(), v[s:], depth+1)`
(natdiv.go:863, `s = B - 1`): `DrsPreW` with window `W - 400`, `z = qhat0`, `u = u[s : s+k]` (cap `uc - s`, `k` = the
normalised length), `v = v[s:]` (the stack arguments); the dividend bound `hval` is supplied by the caller.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem rec_preF {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk k : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s))
    (hvk : X.mem.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)) (hk : k ≤ c.u1 - (c.vl / 2 - 1))
    (hval : 2 * natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) k < 2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))))
    (hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0)
    (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hbud : drsCQ c.ul (c.vl - c.vl / 2 + 1) + stkR c.Hq X.mem c.st ≤ bk)
    (a1 : X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.vp + 8 * (c.vl / 2 - 1))
    (a2 : X.mem.readLE ((s.regs 4).toNat - 384) 8 = c.vl - c.vl / 2 + 1)
    (a3 : X.mem.readLE ((s.regs 4).toNat - 376) 8 = c.vc - (c.vl / 2 - 1)) :
    DrsPreW R bk Lk c.Hq (drsCQ k (c.vl - c.vl / 2 + 1)) (c.W - 400) c.t0 (c.vl / 2 + 1)
      (c.vl / 2 + 1) c.st (c.up + 8 * (c.vl / 2 - 1)) k (c.uc - (c.vl / 2 - 1)) (c.vp + 8 * (c.vl / 2 - 1))
      (c.vl - c.vl / 2 + 1) (c.vc - (c.vl / 2 - 1)) X := by
  have hW := hcr.hW; have hWg := drsW64_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hpre := hcr.pre
  have hsv := hpre.sv; have hgl := hpre.gl
  have hulc := hpre.ulc; have huc := hpre.uc40; have hvlc := hpre.vlc; have hvc := hpre.vc40
  have hvl9 := hpre.v9.1; have htop := hpre.vtop
  obtain ⟨hua, hu48, huh, huo, hug⟩ := hpre.ua
  obtain ⟨hva, hv48, hvh, hvo, hvgA, hvch, hvc48⟩ := hpre.va
  have huv := hpre.uv
  obtain ⟨-, hstw, hstg, harr⟩ := hpre.sti
  obtain ⟨hstl, -, hvcf, hst0⟩ := hpre.stl
  obtain ⟨hus, -⟩ := hpre.su
  obtain ⟨hvs, -⟩ := hpre.sv2
  have hswb := hpre.wbap
  obtain ⟨hq, hugA, hstgA, hfg⟩ := hpre.ga
  obtain ⟨-, hutl, hstl', -⟩ := hpre.tl
  obtain ⟨-, ⟨hb', -, hw⟩, -, -, hout, -, hgr, -⟩ := hpre.ce
  simp only [regSP] at hb' hw
  have hlen := hfp.len
  have hok := hev.sok
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hok.2.2.2.2.2.1
  have hwin : ∀ a n, Outside a n (win s c.W 96) → Outside a n (win X (c.W - 400) 96) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hev.fr.accessible a n w
  -- the globals
  have hglX : RunIface.Globals R X.mem (win X (c.W - 400) 96) := by
    obtain ⟨g1, g2, g3, g4, e1, e2, e3, g5, g6, g7, g8, g9, g10⟩ := hgl
    have rg : ∀ x n, RunIface.gA ≤ x → x + n ≤ RunIface.gA + 32 → X.mem.readLE x n = s.mem.readLE x n := by
      intro x n h1 h2
      refine hev.fr.readLE _ _ ?_
      unfold Apart at hq hugA hstgA hfg
      simp only [win, Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at g7 ⊢
      have g6' := g6.of_sub h1 h2
      and_intros <;> first | exact g6' | omega
    have egA : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
        RunIface.gA := rfl
    refine ⟨by rw [rg _ _ (by omega) (by omega)]; exact g1, by rw [rg _ _ (by omega) (by omega)]; exact g2,
      by rw [rg _ _ (by omega) (by omega)]; exact g3, by rw [egA, rg _ _ (by omega) (by omega), ← egA]; exact g4,
      e1, e2, e3, by rw [hacc]; exact g5, g6, hwin _ _ g7, by rw [hacc]; exact g8, g9, ?_⟩
    simp only [win, outside_cons, outside_nil, and_true] at g10 ⊢; rw [hsp]; omega
  -- the stack's array
  have hstin : DivLarge.StkIn R Lk X (c.W - 400) 96 c.st := by
    refine ⟨hok, hwin _ _ hstw, by rw [h14]; exact hstg, fun hc => ?_⟩
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · simp only [e1, e2] at hc ⊢; obtain ⟨b1, b2⟩ := harr hc; exact ⟨hwin _ _ b1, by rw [h14]; exact b2⟩
    · have h1 := outside_of_inRangesR hout hin
      have h2 := outside_of_inRangesR hgr hin
      refine ⟨?_, ?_⟩
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · rw [h14]; unfold Apart; omega
  -- v top
  have htopX : 2 ^ 63 ≤ X.mem.readLE (c.vp + 8 * (c.vl / 2 - 1) + 8 * (c.vl - c.vl / 2 + 1 - 1)) 8 := by
    rw [show c.vp + 8 * (c.vl / 2 - 1) + 8 * (c.vl - c.vl / 2 + 1 - 1) = c.vp + 8 * (c.vl - 1) by omega,
      rd_sub hvk (by omega) (by omega)]; exact htop
  have t0s := hcr.t0st; have t0u := hcr.t0u; have t0v := hcr.t0v; have t0g := hcr.t0g; have t0gA := hcr.t0gA
  have t0fs := hcr.t0fs
  have fq := hfp.ft0; have fu := hfp.fu; have fv := hfp.fv; have fst := hfp.fst; have fgA := hfp.fgA
  have ffs := hfp.ffs
  rw [← hlen] at fq fu fv fst fgA ffs
  have hvcX : Apart c.vp (8 * c.vc) (stW X.mem c.st + 8 * stLen X.mem c.st)
      (8 * (stCap X.mem c.st - stLen X.mem c.st)) := by
    have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
    rcases free_loc hev hl with ⟨h1, h2⟩ | ⟨hin, hap⟩
    · unfold Apart at hvcf ⊢; omega
    · exact fresh_apart hvch hin hap
  have hlB : stLen X.mem c.st + 12 * (c.vl - c.vl / 2 + 1) + 64 ≤ 2 ^ 16 := by
    rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega
  refine ⟨Ev.callEnv hcr hev hsp h14 hfs (by omega) (by omega), hsv, hglX, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ⟨by omega, by omega⟩, htopX, by simp only [natVal]; exact hq0, hval,
    ⟨by rw [hacc]; exact hcr.t0acc, hcr.t048, hev.ext.held hcr.t0h, hwin _ _ hcr.t0w, by rw [h14]; exact t0g⟩,
    ⟨by rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega), by omega,
      hext.held (huh.sub (by omega) (by omega)), hwin _ _ (huo.of_sub (by omega) (by omega)),
      by rw [h14]; exact apL hug (by omega) (by omega)⟩,
    ⟨by rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hva (by omega) (by omega), by omega,
      hext.held (hvh.sub (by omega) (by omega)), hwin _ _ (hvo.of_sub (by omega) (by omega)),
      apL hvgA (by omega) (by omega), hext.held (hvch.sub (by omega) (by omega)), by omega⟩,
    apR t0u (by omega) (by omega), apR t0v (by omega) (by omega), apR (apL huv (by omega) (by omega)) (by omega) (by omega),
    hstin, ⟨hlB, by rw [hlen] at hlc; simp only [Cx.l1, StackNat.rnd] at hlc; omega, apL hvcX (by omega) (by omega),
      ⟨hst0.1, by have := hst0.2.1; omega, hcr.t0al⟩⟩, ⟨t0s, fq.symm⟩, ⟨apL hus (by omega) (by omega), apL fu.symm (by omega) (by omega)⟩,
    ⟨apL hvs (by omega) (by omega), apL fv.symm (by omega) (by omega)⟩, hswb, fst,
    by rw [hlen]; exact hwin _ _ hfp.fw, ⟨t0gA, apL hugA (by omega) (by omega), hstgA, fgA⟩, ?cost,
    by rw [h14]; exact hev.inv, by rw [hsp, show (s.regs 4).toNat - 400 + 8 = (s.regs 4).toNat - 392 by omega]; exact a1,
    by rw [hsp, show (s.regs 4).toNat - 400 + 16 = (s.regs 4).toNat - 384 by omega]; exact a2,
    by rw [hsp, show (s.regs 4).toNat - 400 + 24 = (s.regs 4).toNat - 376 by omega]; exact a3,
    ⟨by rw [hfs]; exact t0fs, by rw [hfs]; exact apL hutl (by omega) (by omega), by rw [hfs]; exact hstl',
      by rw [hfs]; exact ffs⟩, by rw [hacc]; exact hpre.adx, ?ta⟩
  case ta =>
    intro hc; rw [hfs]
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc; rw [e1, e2]; exact hpre.ta hc
    · have htrt : Outside (s.fsBase.toNat - 8) 8 R.rt := hpre.ce.2.2.2.2.2.2.2.2.2.2.1
      have := outside_of_inRangesR htrt hin; unfold Apart; omega
  case cost =>
    have hcq := hpre.cost.1
    refine ⟨by rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega,
      Nat.le_trans (Nat.add_le_add_right (drsCQ_ul64 _ _ _ (by omega)) _) hbud⟩

end FvModexp.Amd64.Q.DivRec
