import FvModexp.Proofs.Arm64.Nat.DrsCRel
import FvModexp.Proofs.Arm64.Nat.DrsCallS
import FvModexp.Proofs.Arm64.Nat.SubVW
import FvModexp.Proofs.Arm64.Nat.DivOneF

set_option autoImplicit false

/-!
# `divRecursiveStep` (arm64), correction loop: `Mc` across a non-allocating callee (pure)

`Mc.callN`: the correction-loop memory relation `Mc` survives a callee that runs at `X.sp = SP − 400` with stack
window `winA X k a` (`k + 400 ≤ W`, `a ≤ 88`) and writes one range `[p, p+n)` (one of `qhat`, `qhatv`, `uu`): the live
set may grow (`LiveExt`), the budget may grow, and the caller states the new model contents (`qk`/`bf`/`wk`).
`Mc.rdT/rdQ/rdU`: reads of `qhat`/`qhatv`/`uu` sub-ranges apart from `[p, p+n)` are unchanged (to discharge those).
The three region shapes: `Mc.callT` (`qhat`), `Mc.callQ` (`qhatv`), `Mc.callU` (`uu = u[j−B:]`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- a fact hidden from `janus_run` (which destructures every conjunction in the context) -/
structure Box (P : Prop) : Prop where
  h : P


/-- the stack is kept by a callee that only writes `ws` (not the stack) -/
theorem stackBack_keep {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    {wsS ws : List (Nat × Nat)} (hcr : Cr R c s) (h : Ev R c s Lk bk M)
    (hF : MemFrame M M' (R.rt ++ wsS ++ ws)) (hL : LiveFrame M M' Lk ws)
    (hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k wsS) (hst : Outside c.st 24 ws)
    (hx : LiveExt R Lk L') : StackBackL R Lk L' c.st M M' := by
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr h hF hL hS hst
  have hok := stkOK_moveS h.sok eW eL eC hF.accessible
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hok
  exact ⟨⟨⟨h1, hx.held h2, h3, h4, NatDiv.natLive_ext h5 (fun _ _ _ => rfl) hx, h6, h7⟩, eL, Or.inl ⟨eW, eC⟩⟩,
    fun hn => absurd ⟨eW, eC⟩ hn⟩

theorem Rg.ext {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {a n : Nat} (h : Rg R c s Lk a n)
    (hx : LiveExt R Lk L') : Rg R c s L' a n :=
  ⟨hx.held h.h, h.w, h.g, h.st, h.gA, h.q, h.u, h.v, h.t0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`Mc` across a non-allocating callee** writing `[p, p+n)` -/
theorem Mc.callN {R : RtInv} {c : Cx} {s X : State} {Lk L' : List (Nat × Nat)} {bk b' : Nat} {M M' : Memory}
    {j : Nat} {Z U : List Nat} {qv : Nat} {st st' : Mdl.St} {k a p n : Nat}
    (h : Mc R c s Lk bk M j Z U qv st) (hX : X.sp.toNat = s.sp.toNat - 400) (hk : k + 400 ≤ c.W) (ha : a ≤ 88)
    (hF : MemFrame M M' (R.rt ++ winA X k a ++ [(p, p + n)])) (hL : LiveFrame M M' Lk [(p, p + n)])
    (hx : LiveExt R Lk L') (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M')) (hreg : M'.regions = M.regions)
    (hb : bk ≤ b')
    (hW1 : ∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k [(p, p + n)])
    (hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k [(p, p + n)])
    (hw : Outside p n (win s c.W 96)) (hst : Apart c.st 24 p n)
    (hv : Apart c.vp (8 * c.vl) p n) (hut : Apart (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) p n)
    (hz : Apart c.qp (8 * c.ql) p n) (hlk : Apart c.up (8 * (j - c.vl / 2)) p n)
    (hqk : Asm.limbs M' c.t0 (c.q0 s j U).length = st'.qhat) (hbf : Asm.limbs M' qv (3 * c.vl) = st'.buf)
    (hwk : Asm.limbs M' (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) = st'.w) :
    Mc R c s L' b' M' j Z U qv st' := by
  have hcr := h.cr
  have hev := h.ev
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hqh, hqw, -⟩, ⟨-, -, huh, huw, -⟩,
    ⟨-, -, hvh, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', -, -⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hS : ∀ x m, Outside x m (winA s c.W 96) → Outside x m (winA X k a) := fun x m ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hX]; omega
  have hst' : Outside c.st 24 [(p, p + n)] := by
    unfold Apart at hst; simp only [outside_cons, outside_nil, and_true]; omega
  -- the stack-using form of the callee frame
  have hF' : MemFrame M M' (R.rt ++ winA X k a ++ [(p, p + n)] ++ stkWs M c.st) :=
    hF.mono fun x m ho => by simp only [outside_append] at ho ⊢; exact ⟨ho.1.1, ho.1.2⟩
  have hL' : LiveFrame M M' Lk ([(p, p + n)] ++ stkWs M c.st) :=
    SubVW.liveFrame_mono hL fun x m ho => by simp only [outside_append] at ho; exact ho.1
  have hsb := stackBack_keep hcr hev hF hL hS hst' hx
  obtain ⟨eW, -, eC⟩ := hdr_keep hcr hev hF hL hS hst'
  have hl : stLen s.mem c.st ≤ stLen M c.st := by rw [h.fp.len]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' M' := Ev.callS hcr hev hl hF' hL' hS hW1 hW2 hx hinv hsb hreg
  have hFp : Fp R c s L' M' (c.l1 s + StackNat.rnd (3 * c.vl)) :=
    Fp.callS hcr hev h.fp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  have rk : ∀ x m, Held R Lk x m → Outside x m (win s c.W 96) → Outside x m [(p, p + n)] →
      M'.readLE x m = M.readLE x m := fun x m hh hw' ho => keepRd hcr hX hk (by omega) hF hL hh hw' ho
  have oa : ∀ {x m}, Apart x m p n → Outside x m [(p, p + n)] := fun hap => by
    unfold Apart at hap; simp only [outside_cons, outside_nil, and_true]; omega
  have kv := rk _ _ (hext.held hvh) hvw (oa hv)
  have kt := rk _ _ (hext.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega)) (oa hut)
  have kq := rk _ _ (hext.held hqh) hqw (oa hz)
  have hjl : c.up + 8 * (j - c.vl / 2) ≤ c.up + 8 * c.ul := by have := h.li.2.2.2.2.2.2.2; omega
  have kl := rk c.up (8 * (j - c.vl / 2)) (hext.held (huh.sub (Nat.le_refl _) hjl))
    (huw.of_sub (Nat.le_refl _) hjl) (oa hlk)
  have hwl : FixOut s [(p, p + n)] := by
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  have hfo : FixOut s (R.rt ++ winA X k a ++ [(p, p + n)]) := fixOut_callee hout (by omega) (by omega) hX (by omega) hwl
  have hio : IOut s (R.rt ++ winA X k a ++ [(p, p + n)]) := by
    refine iOut_callee hout (by omega) (by omega) hX (by omega) ?_
    simp only [IOut, win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  have hbo : BOut s (R.rt ++ winA X k a ++ [(p, p + n)]) := by
    refine bOut_callee hout (by omega) (by omega) hX (by omega) ?_
    simp only [BOut, win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  have hhi : HiOut s (R.rt ++ winA X k a ++ [(p, p + n)]) :=
    hiOut_callee hout (by omega) (by omega) hX (by omega) (hiOut_win hw (by omega) (by omega))
  exact ⟨hcr, hEv, hFp, h.bd.frame hF hfo hio kv kt kq, h.bs.frame hF hbo, h.jB, h.li, h.q3.frame hF hhi h0',
    h.rg.ext hx, hqk, hbf, hwk, by rw [limbs_congr kl]; exact h.lk, Nat.le_trans h.bud hb,
    by rw [hF.accessible]; exact h.qa, h.qloc, h.qal, Rg.ext (FL.hdr h.fl eW eC) hx⟩

end FvModexp.Arm64.DivRec
