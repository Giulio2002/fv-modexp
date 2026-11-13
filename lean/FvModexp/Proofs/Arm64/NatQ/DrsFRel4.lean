import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsFRel3
import FvModexp.Proofs.Arm64.NatQ.DrsCN
import FvModexp.Proofs.Arm64.Nat.WinIn

/-! (Q-form copy of Arm64/Nat/DrsFRel4.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block segment 4–5: relations of the product and the correction loop (pure)

natdiv.go:867-878: `qhatv = qhatv.mul(stk, qhat, v[:s])`, then `for i := 0; i < 2; i++ { if e := qhatv.cmp(u.norm());
e > 0 { subVW(qhat, qhat, 1); c := subVV(qhatv[:s], qhatv[:s], v[:s]); if len(qhatv) > s { subVW(qhatv[s:], qhatv[s:],
c) }; addTo(u[s:], v[s:]) } }` (no break: `Mdl.corr2`). Adapted from DrsCRel/DrsCN (the iteration's `Mc`/`C`).

* `McF`: the memory facts during the final correction loop at model state `st` (`w` = the whole dividend `u[:u1]`).
* `CF`: the loop head `0x1baab8` (`CMP $2, R3`; `R3 = i`, `R0..R2 = qhatv`).
* `McF.own3` (the stores of `qhatv`'s slots), `McF.callN` (a non-allocating callee writing one range).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

/-- the memory during the final correction loop at model state `st` -/
structure McF (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat)
    (Z U : List Nat) (qv : Nat) (st : Mdl.St) : Prop where
  cr : Cr R c s
  ev : Ev R c s Lk bk M
  fp : Fp R c s Lk M (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : BdF c s M Z
  jB : j ≤ c.vl / 2
  li : c.LI s j Z U
  q3 : QF3 s M (c.qF s U).length
  rg : Rg R c s Lk qv (8 * (3 * c.vl))
  qk : Asm.limbs M c.t0 (c.qF s U).length = st.qhat
  bf : Asm.limbs M qv (3 * c.vl) = st.buf
  wk : Asm.limbs M c.up c.u1 = st.w
  bud : c.lo s + stkR c.Hq M c.st ≤ bk
  qa : M.accessible qv (8 * (3 * c.vl)) true = true
  qloc : Loc R c s qv (8 * (3 * c.vl))
  qal : qv % 8 = 0
  fl : FL R c s Lk M

theorem qF_len {c : Cx} {s : State} {U : List Nat} : (c.qF s U).length ≤ c.vl / 2 + 1 := by
  have e : (c.RF s U).1.length = c.vl / 2 + 1 := by
    simp only [Cx.RF, Mdl.finR, Mdl.recI, Mdl.length_toL, List.length_replicate]
  exact Nat.le_trans (Mdl.length_norm_le _) (Nat.le_of_eq e)

/-- the stores of `qhatv`'s slots in the final block (`SP'+144/160/320`) -/
@[reducible] def is3F (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 256, s.sp.toNat - 248), (s.sp.toNat - 240, s.sp.toNat - 232), (s.sp.toNat - 80, s.sp.toNat - 72)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `McF` across the own stores of `qhatv`'s slots (`is3F`) -/
theorem McF.own3 {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : McF R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (is3F s))
    (hreg : M'.regions = M.regions) : McF R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, is3F, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, is3F, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, is3F, outside_cons, outside_nil, and_true]; omega)
      (by simp only [FOut, is3F, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [is3F, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s200⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.wk, bud_cap (Cr.capOwn hcr hF) h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`McF` across a non-allocating callee** writing `[p, p+n)` -/
theorem McF.callN {R : RtInv} {c : Cx} {s X : State} {Lk L' : List (Nat × Nat)} {bk b' : Nat} {M M' : Memory}
    {j : Nat} {Z U : List Nat} {qv : Nat} {st st' : Mdl.St} {k a p n : Nat}
    (h : McF R c s Lk bk M j Z U qv st) (hX : X.sp.toNat = s.sp.toNat - 400) (hk : k + 400 ≤ c.W) (ha : a ≤ 88)
    (hF : MemFrame M M' (R.rt ++ winA X k a ++ [(p, p + n)])) (hL : LiveFrame M M' Lk [(p, p + n)])
    (hx : LiveExt R Lk L') (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M')) (hreg : M'.regions = M.regions)
    (hb : bk ≤ b')
    (hW1 : ∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k [(p, p + n)])
    (hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k [(p, p + n)])
    (hw : Outside p n (win s c.W 96)) (hst : Apart c.st 24 p n)
    (hv : Apart c.vp (8 * c.vl) p n) (hut : Apart (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) p n)
    (hz : Apart c.qp (8 * c.ql) p n)
    (hqk : Asm.limbs M' c.t0 (c.qF s U).length = st'.qhat) (hbf : Asm.limbs M' qv (3 * c.vl) = st'.buf)
    (hwk : Asm.limbs M' c.up c.u1 = st'.w) :
    McF R c s L' b' M' j Z U qv st' := by
  have hcr := h.cr
  have hev := h.ev
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hqh, hqw, -⟩, ⟨-, -, huh, huw, -⟩,
    ⟨-, -, hvh, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', -, -⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hS : ∀ x m, Outside x m (winA s c.W 96) → Outside x m (winA X k a) := fun _ _ ho =>
    winA_in ho hX (by omega) (by omega) (by omega)
  have hst' : Outside c.st 24 [(p, p + n)] := by
    unfold Apart at hst; simp only [outside_cons, outside_nil, and_true]; omega
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
  have hwl : FixOut s [(p, p + n)] := by
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  have hfo : FixOut s (R.rt ++ winA X k a ++ [(p, p + n)]) := fixOut_callee hout (by omega) (by omega) hX (by omega) hwl
  have hff : FOut s (R.rt ++ winA X k a ++ [(p, p + n)]) := by
    refine fOut_callee hout (by omega) (by omega) hX (by omega) ?_
    simp only [FOut, win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  have hhi : HiOut s (R.rt ++ winA X k a ++ [(p, p + n)]) :=
    hiOut_callee hout (by omega) (by omega) hX (by omega) (hiOut_win hw (by omega) (by omega))
  exact ⟨hcr, hEv, hFp, h.bd.frame hF hfo hff kv kt kq, h.jB, h.li, h.q3.frame hF hhi h0',
    h.rg.ext hx, hqk, hbf, hwk, bud_cap eC (Nat.le_trans h.bud hb),
    by rw [hF.accessible]; exact h.qa, h.qloc, h.qal, Rg.ext (FL.hdr h.fl eW eC) hx⟩

/-- the head of the final correction loop -/
abbrev cHeadF : Nat := 0x1baab8

/-- **the final correction loop's head** after `i` rounds (`0x1baab8`) -/
structure CF (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv i : Nat) (st : Mdl.St) : Prop where
  pc : S.pc = BitVec.ofNat 64 cHeadF
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 qv
  r1 : S.regs 1 = BitVec.ofNat 64 (c.PF s U).length
  r2 : S.regs 2 = BitVec.ofNat 64 (3 * c.vl)
  r3 : S.regs 3 = BitVec.ofNat 64 i
  mc : McF R c s Lk bk S.mem j Z U qv st
  v3 : V3F c s S.mem qv (c.PF s U).length
  hi : i ≤ 2
  inv : Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length (2 - i) st = c.sFF s U

end FvModexp.Arm64.Q.DivRec
