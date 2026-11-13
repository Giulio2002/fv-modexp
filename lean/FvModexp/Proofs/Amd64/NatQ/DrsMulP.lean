import FvModexp.Proofs.Amd64.NatQ.DrsA3
import FvModexp.Proofs.Amd64.NatQ.DrsRecP
import FvModexp.Proofs.Amd64.NatQ.MulHypQE

set_option autoImplicit false

/-! (amd64 twin (asm s48) of Arm64/NatQ/DrsMulP.lean)
# `divRecursiveStep` (amd64), loop body: the precondition of `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831; pure)

`mul_pre`: at the callee entry `X` (`RSP = r - 400`, memory = `A3`'s): divmc's `Q.NatMul.MPre` (window `W'`,
`mulW64 qn (B-1) ≤ W'`, `W' + 400 ≤ W`, above `88`) with `z = qhatv (qv, 3n)`, `x = qhat (t0, qn, cap B+1)`,
`y = v[:B-1] (vp, B-1, cap vc)`, reserve level `Hq`, budget `bk`.
The whole entry stack array is apart from the TLS slot by `DrsPreW.ta` (asm s49; `StkPre` needs it for the whole array).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem mul_pre {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk qn W' : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s + StackNat.rnd (3 * c.vl)))
    (hrg : Rg R c s Lk (c.qv s X.mem) (8 * (3 * c.vl))) (hqle : qn ≤ c.vl / 2 + 1)
    (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hk : mulW64 qn (c.vl / 2 - 1) ≤ W') (hkW : W' + 400 ≤ c.W)
    (hbud : mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq X.mem c.st ≤ bk) :
    Q.NatMul.MPre R bk c.Hq Lk W' (c.qv s X.mem) (3 * c.vl) c.st c.t0 qn (c.vl / 2 + 1) c.vp (c.vl / 2 - 1)
      c.vc X := by
  have hW := hcr.hW; have hWg := drsW64_ge c.vl; have h40 := hcr.h40
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hpre := hcr.pre
  have hsv := hpre.sv; have hgl := hpre.gl
  have hvlc := hpre.vlc; have hvc := hpre.vc40
  have hvl9 := hpre.v9.1
  obtain ⟨hva, hv48, hvh, hvo, hvgA, hvch, hvc48⟩ := hpre.va
  obtain ⟨-, hstw, hstg, harr⟩ := hpre.sti
  obtain ⟨hstl, -, -, hst0⟩ := hpre.stl
  obtain ⟨hvs, -⟩ := hpre.sv2
  have hswb := hpre.wbap
  obtain ⟨hq, hugA, hstgA, hfg⟩ := hpre.ga
  obtain ⟨-, -, hstl', -⟩ := hpre.tl
  have hcH := hpre.cost.1
  have hce0 := hpre.ce
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, hgr, -, hro, ⟨-, htrt, -⟩⟩ := hce0
  simp only [regSP] at hb'
  have hlen := hfp.len
  have hok := hev.sok
  have hwin : ∀ a n, Outside a n (win s c.W 96) → Outside a n (win X W' 88) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hev.fr.accessible a n w
  -- the globals
  have hglX : RunIface.Globals R X.mem (win X W' 88) := by
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
  have hty : Outside NatAdd.wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  -- the stack's array
  have hnl := hok.2.2.2.2.1
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hok.2.2.2.2.2.1
  have hlX : stLen X.mem c.st = stLen s.mem c.st + StackNat.rnd (c.vl / 2 + 1) + StackNat.rnd (3 * c.vl) := by
    rw [hlen]
  simp only [StackNat.rnd] at hlX
  have hn : 0 < stCap X.mem c.st := by omega
  obtain ⟨harr8, -, harrA, harr48⟩ := hnl hn
  have harrX : Outside (stW X.mem c.st) (8 * stCap X.mem c.st) (win X W' 88) ∧
      Apart (stW X.mem c.st) (8 * stCap X.mem c.st) ((X.regs 14).toNat + 16) 8 ∧
      Apart (stW X.mem c.st) (8 * stCap X.mem c.st) (X.fsBase.toNat - 8) 8 := by
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · have hn' : 0 < stCap s.mem c.st := by rw [← e2]; exact hn
      rw [e1, e2]; obtain ⟨b1, b2⟩ := harr hn'
      exact ⟨hwin _ _ b1, by rw [h14]; exact b2, by rw [hfs]; exact hcr.pre.ta hn'⟩
    · have h1 := outside_of_inRangesR hout hin
      have h2 := outside_of_inRangesR hgr hin
      have h3 := outside_of_inRangesR htrt hin
      refine ⟨?_, ?_, ?_⟩
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · rw [h14]; unfold Apart; omega
      · rw [hfs]; unfold Apart; omega
  have t0s := hcr.t0st; have t0gA := hcr.t0gA
  have fq := hfp.ft0; have fv := hfp.fv; have fst := hfp.fst; have fgA := hfp.fgA; have fh := hfp.fh
  have ffw := hfp.fw; have ffg := hfp.fg; have ffs := hfp.ffs
  rw [← hlen] at fq fv fst fgA fh ffw ffg ffs
  have rg8 := hrg.t0; have rgv := hrg.v; have rgst := hrg.st
  have hqv : c.qv s X.mem + 8 * (3 * c.vl) ≤ stW X.mem c.st + 8 * stLen X.mem c.st := by
    simp only [Cx.qv, Cx.l1, StackNat.rnd]; omega
  have hqv0 : stW X.mem c.st ≤ c.qv s X.mem := by simp only [Cx.qv]; omega
  have hta : X.mem.accessible c.t0 (8 * qn) false = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hcr.t0acc)
      (Nat.le_refl _) (by omega)
  have hva' : X.mem.accessible c.vp (8 * (c.vl / 2 - 1)) false = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hva (Nat.le_refl _) (by omega)
  have hcost : stLen X.mem c.st + 4 * (qn + (c.vl / 2 - 1)) + 64 ≤ c.Hq ∧
      mulCQ qn (c.vl / 2 - 1) + stkR c.Hq X.mem c.st ≤ bk := by
    refine ⟨by omega, Nat.le_trans (Nat.add_le_add_right (mulCQ_mono hqle (Nat.le_refl _)) _) hbud⟩
  unfold Q.NatMul.MPre Q.NatMul.Ops Q.NatSqr.StkPre Q.NatSqr.StkSep Q.NatSqr.guard Q.NatSqr.tls
  simp only [BasicSqr.freeP, BasicSqr.freeN]
  refine ⟨Ev.callEnv hcr hev hsp h14 hfs (by omega) (by omega), hk, hsv, hglX, hty,
    ⟨⟨hqle, by omega, by omega, fun _ => hta, fun _ => ⟨hev.ext.held hcr.t0h, hcr.t048⟩,
      fun _ => ⟨hwin _ _ (hcr.t0w.of_sub (Nat.le_refl _) (by omega)),
        ?t0st, apL fq.symm (Nat.le_refl _) (by omega),
        apL t0gA (Nat.le_refl _) (by omega)⟩⟩,
     ⟨by omega, hvc, by omega, fun _ => hva', fun _ => ⟨hext.held hvch, hvc48⟩,
      fun _ => ⟨hwin _ _ (hvo.of_sub (Nat.le_refl _) (by omega)), ?vst, apL fv.symm (Nat.le_refl _) (by omega),
        apL hvgA (Nat.le_refl _) (by omega)⟩⟩,
     ⟨by omega, fun _ => ⟨?qal, hrg.h, ?qacc, by omega⟩, hwin _ _ hrg.w,
      fun _ => ⟨by rw [h14]; exact hrg.g, by rw [hfs]; exact hrg.fs, rgst, ?qfree, hrg.gA⟩,
      Or.inr fun _ _ => apR rg8 (Nat.le_refl _) (by omega), Or.inr fun _ _ => apR rgv (Nat.le_refl _) (by omega)⟩,
     by omega⟩,
    ⟨hst0.1, hok, hwin _ _ hstw, by rw [h14]; exact hstg, fun _ => ⟨harrX.1, harrX.2.1⟩, by rw [h14]; exact ffg,
      hwin _ _ ffw, fst, hswb, fh, hstgA, fgA, by rw [hfs]; exact hstl', fun _ => harrX.2.2, by rw [hfs]; exact ffs⟩,
    hcost, by rw [hacc]; exact hpre.adx, by rw [h14]; exact hev.inv⟩
  case t0st => unfold Apart at t0s ⊢; omega
  case vst => unfold Apart at hvs ⊢; omega
  case qal => simp only [Cx.qv]; omega
  case qacc => exact Janus.Arm64.Memory.accessible_mono _ harrA (by omega) (by omega)
  case qfree => unfold Apart; omega

end FvModexp.Amd64.Q.DivRec
