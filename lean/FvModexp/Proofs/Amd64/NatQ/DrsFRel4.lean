import FvModexp.Proofs.Amd64.NatQ.DrsFRel3
import FvModexp.Proofs.Amd64.NatQ.DrsCN

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsFRel4.lean; adapted from Amd64/NatQ/DrsCRel.lean, DrsCN.lean)
# `divRecursiveStep` (amd64), final block: the relations of the final correction loop (pure)

* `McF`: the memory facts from `qhatv.mul(stk, qhat, v[:s])` on (model state `st`: `qhat`, `qhatv`'s buffer, `u`).
* `is3F`/`McF.own3`: the stores of `qhatv`'s slots after the call (`0x138/0x80/0x90(SP)` = `r-80`, `r-264`, `r-248`).
* `McF.callN`: `McF` across a non-allocating callee writing one range.
* `CF`: the head `0x5f0360` of `for i := 0; i < 2; i++` (`RDX = i`; `RAX/RBX/RCX = qhatv`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the memory facts of the final block from `qhatv.mul(…)` on -/
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


/-- the stores of `qhatv`'s slots in the final block (`0x80/0x90/0x138(SP)`) -/
@[reducible] def is3F (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 264, (s.regs 4).toNat - 256), ((s.regs 4).toNat - 248, (s.regs 4).toNat - 240),
    ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `McF` across the own stores of `qhatv`'s slots (`is3`) -/
theorem McF.own3 {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : McF R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (is3F s))
    (hreg : M'.regions = M.regions) : McF R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, win, is3F, outside_cons, outside_nil, and_true] at ho ⊢; omega
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
    (h : McF R c s Lk bk M j Z U qv st) (hX : (X.regs 4).toNat = (s.regs 4).toNat - 400) (hk : k + 400 ≤ c.W)
    (ha : a ≤ 103)
    (hF : MemFrame M M' (R.rt ++ win X k a ++ [(p, p + n)])) (hL : LiveFrame M M' Lk [(p, p + n)])
    (hx : LiveExt R Lk L') (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M')) (hreg : M'.regions = M.regions)
    (hb : bk ≤ b')
    (hW1 : ∀ x k, Outside x k (R.rt ++ win s c.W 96 ++ c.ws s) → Outside x k [(p, p + n)])
    (hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k [(p, p + n)])
    (hw : Outside p n (win s c.W 96)) (hst : Apart c.st 24 p n)
    (hv : Apart c.vp (8 * c.vl) p n) (hut : Apart (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) p n)
    (hz : Apart c.qp (8 * c.ql) p n)
    (hqk : Asm.limbs M' c.t0 (c.qF s U).length = st'.qhat) (hbf : Asm.limbs M' qv (3 * c.vl) = st'.buf)
    (hwk : Asm.limbs M' c.up c.u1 = st'.w) :
    McF R c s L' b' M' j Z U qv st' := by
  have hcr := h.cr
  have hev := h.ev
  have hpre := hcr.pre
  obtain ⟨-, -, hqh, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvw, -, -, -⟩ := hpre.va
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb'
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hS : ∀ x m, Outside x m (win s c.W 96) → Outside x m (win X k a) := fun x m ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hX]; omega
  have hst' : Outside c.st 24 [(p, p + n)] := by
    unfold Apart at hst; simp only [outside_cons, outside_nil, and_true]; omega
  -- the stack-using form of the callee frame
  have hF' : MemFrame M M' (R.rt ++ win X k a ++ [(p, p + n)] ++ stkWs M c.st) :=
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
  have hfo : FixOut s (R.rt ++ win X k a ++ [(p, p + n)]) := fixOut_callee hout (by omega) (by omega) hX (by omega) hwl
  have hio : FOut s (R.rt ++ win X k a ++ [(p, p + n)]) := by
    refine fOut_callee hout (by omega) (by omega) hX (by omega) ?_
    simp only [FOut, win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  have hhi : HiOut s (R.rt ++ win X k a ++ [(p, p + n)]) :=
    hiOut_callee hout (by omega) (by omega) hX (by omega) (hiOut_win hw (by omega) (by omega))
  exact ⟨hcr, hEv, hFp, h.bd.frame hF hfo hio kv kt kq, h.jB, h.li, h.q3.frame hF hhi h0',
    h.rg.ext hx, hqk, hbf, hwk, bud_cap eC (Nat.le_trans h.bud hb),
    by rw [hF.accessible]; exact h.qa, h.qloc, h.qal, Rg.ext (FL.hdr h.fl eW eC) hx⟩

/-- the head of the final correction loop (`CMPQ DX, $0x2`) -/
abbrev cHeadF : Nat := 0x5f0360

/-- **the final correction loop's head** after `i` rounds (`0x5f0360`) -/
structure CF (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv i : Nat) (st : Mdl.St) : Prop where
  pc : S.rip = BitVec.ofNat 64 cHeadF
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  r0 : S.regs 0 = BitVec.ofNat 64 qv
  r3 : S.regs 3 = BitVec.ofNat 64 (c.PF s U).length
  r1 : S.regs 1 = BitVec.ofNat 64 (3 * c.vl)
  r2 : S.regs 2 = BitVec.ofNat 64 i
  mc : McF R c s Lk bk S.mem j Z U qv st
  v3 : V3F c s S.mem qv (c.PF s U).length
  hi : i ≤ 2
  inv : Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length (2 - i) st = c.sFF s U

end FvModexp.Amd64.Q.DivRec
