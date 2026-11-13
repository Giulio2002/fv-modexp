import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsA3

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsMulP.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), loop body: the precondition of `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831; pure)

`mul_pre`: at the call state `X` (`SP = entry SP - 400`, memory = `A3`'s): `EvenHyp.MulPre` (+ `CapIn` of both operands,
`MulX`) of `nat.mul` with `z = qhatv (qv, 3n, 3n)`, `x = qhat (t0, qn, cap B+1)`, `y = v[:B-1] (vp, B-1, cap vc)`, any
window `stkM ≤ mulWX`, `aboveM ≤ 88`, budget `mulC (stack length) qn (B-1)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

theorem apL' {a n b k a' n' : Nat} (h : Apart a n b k) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Apart a' n' b k := by
  unfold Apart at h ⊢; omega

theorem apR' {a n b k b' k' : Nat} (h : Apart a n b k) (h1 : b ≤ b') (h2 : b' + k' ≤ b + k) : Apart a n b' k' := by
  unfold Apart at h ⊢; omega

set_option maxHeartbeats 16000000 in
theorem mul_pre {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk qn stkM aboveM K0 : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s + StackNat.rnd (3 * c.vl)))
    (hrg : Rg R c s Lk (c.qv s X.mem) (8 * (3 * c.vl))) (hqle : qn ≤ c.vl / 2 + 1)
    (hsp : X.sp.toNat = s.sp.toNat - 400) (h28 : X.regs 28 = s.regs 28) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hbud : K0 + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq X.mem c.st ≤ bk) :
    EvenHyp.MulPre R bk (mulCQ qn (c.vl / 2 - 1) + stkR c.Hq X.mem c.st) Lk stkM aboveM (c.qv s X.mem) (3 * c.vl)
        (3 * c.vl) c.st c.t0 qn c.vp (c.vl / 2 - 1) X ∧
      EvenHyp.CapIn R Lk c.t0 qn (c.vl / 2 + 1) ∧ EvenHyp.CapIn R Lk c.vp (c.vl / 2 - 1) c.vc ∧
      EvenHyp.MulX R Lk X stkM aboveM c.st (c.qv s X.mem) (3 * c.vl) c.t0 qn (c.vl / 2 + 1) c.vp (c.vl / 2 - 1)
        c.vc ∧ stLen X.mem c.st + 4 * (qn + (c.vl / 2 - 1)) + 64 ≤ c.Hq := by
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hk' : stkM ≤ 30208 := hk
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, hsv, hgl, -, -, -, -, hvlc, hvc, -, ⟨hvl9, -⟩, -, -, -,
    ⟨-, -, -, -, -⟩, -, ⟨hva, hv48, hvh, hvo, hvgA, hvch, hvc48⟩, -, -, -,
    ⟨-, hstw, hstg, harr⟩, ⟨hstl, -, -, hst0⟩, -, -, ⟨hvs, -⟩, hswb, -, -, ⟨hq, hugA, hstgA, hfg⟩, hcq, -⟩ := hcr.pre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', -, hw⟩, -, hout, hga, hgr, -, -⟩ := hce'
  have hlen := hfp.len
  have hok := hev.sok
  obtain ⟨-, -, -, -, hnl, hlc, -⟩ := hok
  have hlen' := hlen
  simp only [Cx.l1, StackNat.rnd] at hlen'
  have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
  have hn : 0 < stCap X.mem c.st := by omega
  obtain ⟨harr8, -, harrA, harr48⟩ := hnl hn
  have hwin : ∀ a n, Outside a n (win s c.W 96) → Outside a n (win X stkM aboveM) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hev.fr.accessible a n w
  -- the globals
  have hglX : RunIface.Globals R X.mem (win X stkM aboveM) := by
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
  -- the stack
  have hstin : EvenHyp.StkIn R Lk X stkM aboveM c.st := by
    refine ⟨hev.sok, hwin _ _ hstw, by rw [h28]; exact hstg, fun hc => ?_⟩
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · simp only [e1, e2] at hc ⊢; obtain ⟨a1, a2⟩ := harr hc; exact ⟨hwin _ _ a1, by rw [h28]; exact a2⟩
    · have h1 := FvModexp.Arm64.NatAdd.outside_of_inRanges hout hin
      have h2 := FvModexp.Arm64.NatAdd.outside_of_inRanges hgr hin
      refine ⟨?_, ?_⟩
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · rw [h28]; unfold Apart; omega
  have t0s := hcr.t0st; have t0gA := hcr.t0gA
  have fq := hfp.ft0; have fv := hfp.fv; have fst := hfp.fst; have fgA := hfp.fgA; have fh := hfp.fh
  have ffw := hfp.fw; have ffg := hfp.fg
  rw [← hlen] at fq fv fst fgA fh ffw ffg
  have rg8 := hrg.t0; have rgv := hrg.v; have rgst := hrg.st
  have hqv : c.qv s X.mem + 8 * (3 * c.vl) ≤ stW X.mem c.st + 8 * stLen X.mem c.st := by
    simp only [Cx.qv]; omega
  have hta : X.mem.accessible c.t0 (8 * qn) false = true := by
    rw [hacc]; exact Memory.accessible_mono _ (Memory.accessible_read_of_write _ hcr.t0acc) (Nat.le_refl _) (by omega)
  have hva' : X.mem.accessible c.vp (8 * (c.vl / 2 - 1)) false = true := by
    rw [hacc]; exact Memory.accessible_mono _ hva (Nat.le_refl _) (by omega)
  refine ⟨⟨Ev.callEnv hcr hev hsp h28 (by omega) (by omega), hsv, hglX, Nat.le_refl _,
    ⟨by omega, fun _ => ⟨(by simp only [Cx.qv]; omega), hrg.h,
      Memory.accessible_mono _ harrA (by simp only [Cx.qv]; omega) (by omega), by omega⟩,
      fun _ => ⟨hwin _ _ hrg.w, (by rw [h28]; exact hrg.g)⟩⟩,
    ⟨by omega, hta, (by have := hcr.t048; omega),
      (hev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega), hwin _ _ (hcr.t0w.of_sub (Nat.le_refl _) (by omega))⟩,
    ⟨by omega, hva', by omega,
      hext.held (hvh.sub (Nat.le_refl _) (by omega)), hwin _ _ (hvo.of_sub (Nat.le_refl _) (by omega))⟩,
    by omega, by omega, Or.inr fun _ _ => apR' rg8 (Nat.le_refl _) (by omega),
    Or.inr fun _ _ => apR' rgv (Nat.le_refl _) (by omega), hstin, by omega,
    fun _ => ⟨rgst.symm, fun _ => (by unfold Apart; omega)⟩,
    fun _ => ⟨apL' t0s (Nat.le_refl _) (by omega), fun _ => apL' fq.symm (Nat.le_refl _) (by omega)⟩,
    fun _ => ⟨apL' hvs (Nat.le_refl _) (by omega), fun _ => apL' fv.symm (Nat.le_refl _) (by omega)⟩,
    ?cost, (by rw [h28]; exact hev.inv)⟩,
    ⟨hqle, by omega, hev.ext.held hcr.t0h, hcr.t048⟩, ⟨by omega, hvc, hext.held hvch, hvc48⟩,
    ⟨⟨hst0.1, hswb, fh, hwin _ _ ffw, (by rw [h28]; exact ffg), fst, hstgA, fgA⟩, hwin _ _ hrg.w,
    fun e => (by unfold Apart at rg8; simp only [Cx.qv] at e rg8; omega),
    fun e => (by unfold Apart at rgv; simp only [Cx.qv] at e rgv; omega),
    fun _ => ⟨(by unfold Apart; simp only [EvenHyp.frP, EvenHyp.frN]; omega), hrg.gA⟩,
    fun _ => ⟨apL' fq.symm (Nat.le_refl _) (by omega), apL' t0gA (Nat.le_refl _) (by omega)⟩,
    fun _ => ⟨apL' fv.symm (Nat.le_refl _) (by omega), apL' hvgA (Nat.le_refl _) (by omega)⟩⟩, ?lvl⟩
  case cost =>
    exact Nat.le_trans (Nat.add_le_add_right (mulCQ_mono hqle (Nat.le_refl _)) _) (by omega)
  case lvl =>
    rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega

end FvModexp.Arm64.Q.DivRec
