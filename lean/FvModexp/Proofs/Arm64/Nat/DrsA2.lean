import FvModexp.Proofs.Arm64.Nat.DrsRecQ

/-!
# `divRecursiveStep` (arm64), loop body: after the recursive call (pure)

* `Bs c s M j`: the seven argument slots of the recursive call that the rest of the iteration reads again
  (`s = B - 1` @`SP'+136`, `uu[s:]` ptr/cap @`376`/`288`, `j` @`280`, `v[s:]` ptr/len/cap @`368`/`264`/`272`);
  `BOut`, `bOut_callee`, `fo504` (a range outside the own frame avoids every fixed/iteration/argument slot).
* `keepP`: a held range apart from the callee's writes keeps its bytes over the recursive call.
* `rec_post`: `Ev`/`Fp`/`Bd`/`Bs`, the lists (`Mdl.blockR Mdl.recI`) and the budget after the recursive call, from
  `DrsPostW`.
* `A2`: the state at the return `0x1ba614` of the recursive call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the argument slots of the recursive call (read again by the correction loop and `nat.mul`) -/
structure Bs (c : Cx) (s : State) (M : Memory) (j : Nat) : Prop where
  b1 : M.readLE (s.sp.toNat - 264) 8 = c.vl / 2 - 1
  ucap : M.readLE (s.sp.toNat - 112) 8 = c.uc - j + 1
  uptr : M.readLE (s.sp.toNat - 24) 8 = c.up + 8 * (j - 1)
  jj : M.readLE (s.sp.toNat - 120) 8 = j
  vcap : M.readLE (s.sp.toNat - 128) 8 = c.vc - c.vl / 2 + 1
  vlen : M.readLE (s.sp.toNat - 136) 8 = c.vl - c.vl / 2 + 1
  vptr : M.readLE (s.sp.toNat - 32) 8 = c.vp + 8 * (c.vl / 2 - 1)

/-- `rs` avoids the argument slots -/
@[reducible] def BOut (s : State) (rs : List (Nat × Nat)) : Prop :=
  Outside (s.sp.toNat - 264) 8 rs ∧ Outside (s.sp.toNat - 136) 24 rs ∧ Outside (s.sp.toNat - 112) 8 rs ∧
    Outside (s.sp.toNat - 32) 16 rs

theorem Bs.frame {c : Cx} {s : State} {M M' : Memory} {j : Nat} {rs : List (Nat × Nat)} (h : Bs c s M j)
    (hF : MemFrame M M' rs) (ho : BOut s rs) : Bs c s M' j := by
  obtain ⟨o1, o2, o3, o4⟩ := ho
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N → M'.readLE x n = M.readLE x n :=
    fun hA h1 h2 => hF.readLE _ _ (hA.of_sub h1 h2)
  exact ⟨by rw [r o1 (by omega) (by omega)]; exact h.b1, by rw [r o3 (by omega) (by omega)]; exact h.ucap,
    by rw [r o4 (by omega) (by omega)]; exact h.uptr, by rw [r o2 (by omega) (by omega)]; exact h.jj,
    by rw [r o2 (by omega) (by omega)]; exact h.vcap, by rw [r o2 (by omega) (by omega)]; exact h.vlen,
    by rw [r o4 (by omega) (by omega)]; exact h.vptr⟩

/-- a callee frame `R.rt ++ winA S k a ++ ws` (`S.sp = SP - 400`, `a ≤ 103`) avoids the argument slots when `ws`
does -/
theorem bOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside (s.sp.toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - 400) (ha : a ≤ 103) (hws : BOut s ws) :
    BOut s (R.rt ++ winA S k a ++ ws) := by
  obtain ⟨w1, w2, w3, w4⟩ := hws
  have o : ∀ x n, s.sp.toNat - 408 ≤ x → x + n ≤ s.sp.toNat + 96 → Outside x n R.rt :=
    fun x n h1 h2 => hout.of_sub (by omega) (by omega)
  simp only [BOut, winA, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  exact ⟨⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w1⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w2⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w3⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w4⟩⟩

/-- ranges outside the own frame avoid every fixed, iteration and argument slot -/
theorem fo504 {s : State} {rs : List (Nat × Nat)} (h : Outside (s.sp.toNat - 408) 504 rs) (h0 : 408 ≤ s.sp.toNat) :
    FixOut s rs ∧ IOut s rs ∧ BOut s rs := by
  have o : ∀ x n, s.sp.toNat - 408 ≤ x → x + n ≤ s.sp.toNat + 96 → Outside x n rs :=
    fun x n h1 h2 => h.of_sub (by omega) (by omega)
  exact ⟨⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega),
      o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega),
      o _ _ (by omega) (by omega), o _ _ (by omega) (by omega)⟩,
    ⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega)⟩,
    ⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega),
      o _ _ (by omega) (by omega)⟩⟩

theorem out504 {s : State} {W x n : Nat} (h : Outside x n (win s W 96)) (hW : 408 ≤ W) (h0 : W ≤ s.sp.toNat) :
    Outside (s.sp.toNat - 408) 504 [(x, x + n)] := by
  simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega

theorem apS {a n b k a' n' : Nat} (h : Apart a n b k) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Apart a' n' b k := by
  unfold Apart at h ⊢; omega

/-- the writes of the recursive call of iteration `j` (its `z` = `qhat0` and `u = uu[s:B+n]`) -/
@[reducible] def wsR (c : Cx) (j : Nat) : List (Nat × Nat) :=
  [(c.t0, c.t0 + 8 * (c.vl / 2 + 1)), (c.up + 8 * (j - 1), c.up + 8 * (j - 1) + 8 * (c.vl + 1))]

/-- a range apart from the recursive call's writes keeps its bytes -/
theorem keepP {R : RtInv} {c : Cx} {s X X' : State} {Lk : List (Nat × Nat)} {j x n : Nat}
    (hcr : Cr R c s) (hsp : X.sp.toNat = s.sp.toNat - 400)
    (hF : MemFrame X.mem X'.mem (R.rt ++ winA X (c.W - 400) 96 ++ (wsR c j ++ stkWs X.mem c.st)))
    (hL : LiveFrame X.mem X'.mem Lk (wsR c j ++ stkWs X.mem c.st)) (hh : Held R Lk x n)
    (hw : Outside x n (win s c.W 96)) (h1 : Apart x n c.t0 (8 * (c.vl / 2 + 1)))
    (h2 : x + n ≤ c.up + 8 * (j - 1) ∨ c.up + 8 * (j - 1) + 8 * (c.vl + 1) ≤ x) (h3 : Apart x n c.st 24)
    (h4 : Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)))
    (hlc : stLen X.mem c.st ≤ stCap X.mem c.st) :
    X'.mem.readLE x n = X.mem.readLE x n := by
  have hW := hcr.hW; have := drsW_ge c.vl
  refine keepRd hcr hsp (by omega) (by omega) hF hL hh hw ?_
  unfold Apart at h1 h3 h4
  simp only [wsR, stkWs, outside_append, outside_cons, outside_nil, and_true]
  omega

/-- the lists and facts after the recursive call -/
@[reducible] def Cx.R (c : Cx) (s : State) (j : Nat) (U : List Nat) : List Nat × List Nat :=
  Mdl.blockR Mdl.recI (c.V s) c.vl (c.vl / 2) j U

set_option maxHeartbeats 16000000 in
/-- **after the recursive call** (pure) -/
theorem rec_post {R : RtInv} {c : Cx} {s X X' : State} {Lk : List (Nat × Nat)} {bk j : Nat} {Z U : List Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s)) (hbd : Bd c s X.mem j Z)
    (hbs : Bs c s X.mem j) (hj : c.vl / 2 < j) (hjm : j ≤ c.u1 - c.vl) (huk : Asm.limbs X.mem c.up c.u1 = U)
    (hsp : X.sp.toNat = s.sp.toNat - 400) (h28 : X.regs 28 = s.regs 28) (hbud : c.lo s + (j / (c.vl / 2) + 1) * c.K s ≤ bk)
    (hpost : DrsPostW R bk Lk (drsC (stLen X.mem c.st) (c.vl + 1) (c.vl - c.vl / 2 + 1)) (c.W - 400) c.t0
      (c.vl / 2 + 1) c.st (c.up + 8 * (j - 1)) (c.vl + 1) (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) X X')
    (hreg : X'.mem.regions = X.mem.regions) :
    ∃ L' b', Ev R c s L' b' X'.mem ∧ Fp R c s L' X'.mem (c.l1 s) ∧ Bd c s X'.mem j Z ∧ Bs c s X'.mem j ∧
      Asm.limbs X'.mem c.t0 (c.vl / 2 + 1) = (c.R s j U).1 ∧
      Asm.limbs X'.mem c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2 ∧
      c.lo s + (j / (c.vl / 2)) * c.K s + stackNatCost (c.l1 s) (3 * c.vl) +
        mulC (c.l1 s + StackNat.rnd (3 * c.vl)) (c.vl / 2 + 1) (c.vl / 2 - 1) ≤ b' := by
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, hqh, hqo, -⟩, ⟨-, -, huh, huo, -⟩, ⟨-, -, hvh, hvo, -, -, -⟩, -, -, huv,
    ⟨-, hstw, -, -⟩, -, ⟨hqs, -⟩, ⟨hus, -⟩, ⟨hvs, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨hq, hr, L', b', ⟨hx, hb', hinv⟩, hsb, hMF, hLF⟩ := hpost
  have hMF' : MemFrame X.mem X'.mem (R.rt ++ winA X (c.W - 400) 96 ++ (wsR c j ++ stkWs X.mem c.st)) := by
    rw [← List.append_assoc]; exact hMF
  have hlen := hfp.len
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hev.sok.2.2.2.2.2.1
  have fq := hfp.fq; have fu := hfp.fu; have fv := hfp.fv; have ffw := hfp.fw
  rw [← hlen] at fq fu fv ffw
  have h0 : 408 ≤ s.sp.toNat := by omega
  -- the callee's writes avoid the own slots
  have hws504 : Outside (s.sp.toNat - 408) 504 (wsR c j ++ stkWs X.mem c.st) := by
    have a1 := out504 hcr.t0w (by omega) (by omega)
    have a2 := out504 (huo.of_sub (a := c.up + 8 * (j - 1)) (n := 8 * (c.vl + 1)) (by omega) (by omega)) (by omega) (by omega)
    have a3 := out504 hstw (by omega) (by omega)
    have a4 := out504 ffw (by omega) (by omega)
    simp only [wsR, stkWs, outside_append, outside_cons, outside_nil, and_true] at a1 a2 a3 a4 ⊢
    refine ⟨⟨a1, a2⟩, a3, ?_⟩
    rw [show stW X.mem c.st + 8 * stCap X.mem c.st = stW X.mem c.st + 8 * stLen X.mem c.st +
      8 * (stCap X.mem c.st - stLen X.mem c.st) by omega]; exact a4
  obtain ⟨fo, io, bo⟩ := fo504 hws504 h0
  -- reads kept
  have kp : ∀ {x n : Nat}, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.t0 (8 * (c.vl / 2 + 1)) →
      (x + n ≤ c.up + 8 * (j - 1) ∨ c.up + 8 * (j - 1) + 8 * (c.vl + 1) ≤ x) → Apart x n c.st 24 →
      Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)) →
      X'.mem.readLE x n = X.mem.readLE x n := fun hh hw' h1 h2 h3 h4 =>
    keepP hcr hsp hMF' hLF hh hw' h1 h2 h3 h4 hlc
  have t0q := hcr.t0q; have t0u := hcr.t0u; have t0v := hcr.t0v
  have kv : X'.mem.readLE c.vp (8 * c.vl) = X.mem.readLE c.vp (8 * c.vl) :=
    kp (hext.held hvh) hvo t0v.symm (by unfold Apart at huv; omega) hvs fv.symm
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul →
      (x + n ≤ c.up + 8 * (j - 1) ∨ c.up + 8 * (j - 1) + 8 * (c.vl + 1) ≤ x) →
      X'.mem.readLE x n = X.mem.readLE x n := fun x n h1 h2 h3 =>
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apS t0u.symm h1 h2) h3 (apS hus h1 h2) (apS fu.symm h1 h2)
  have kz : X'.mem.readLE c.qp (8 * c.ql) = X.mem.readLE c.qp (8 * c.ql) :=
    kp (hext.held hqh) hqo t0q.symm (by
      have := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; unfold Apart at this; omega) hqs fq.symm
  -- environment
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k (winA X (c.W - 400) 96) := fun x k ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hsp]; omega
  have hW1 : ∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k (wsR c j) := fun x k ho => by
    have a1 := hloc.1 x k ho
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho a1 ⊢
    exact ⟨a1, by omega⟩
  have hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k (wsR c j) := fun x k hin ho => by
    have a1 := hloc.2 x k hin ho
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho a1 ⊢
    exact ⟨a1, by omega⟩
  have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' X'.mem := Ev.callS hcr hev hl hMF hLF hS hW1 hW2 hx (by rw [← h28]; exact hinv) hsb hreg
  have hFp : Fp R c s L' X'.mem (c.l1 s) :=
    Fp.callS hcr hev hfp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  have hBd : Bd c s X'.mem j Z := hbd.frame hMF'
    (fixOut_callee hout (by omega) (by omega) hsp (by omega) fo)
    (iOut_callee hout (by omega) (by omega) hsp (by omega) io) kv
    (ku _ _ (by omega) (by omega) (Or.inr (by omega))) kz
  have hBs : Bs c s X'.mem j := hbs.frame hMF' (bOut_callee hout (by omega) (by omega) hsp (by omega) bo)
  -- values
  have hv0 : X.mem.readLE (c.vp + 8 * (c.vl / 2 - 1)) (8 * (c.vl - c.vl / 2 + 1)) =
      s.mem.readLE (c.vp + 8 * (c.vl / 2 - 1)) (8 * (c.vl - c.vl / 2 + 1)) :=
    rd_sub hbd.vk (by omega) (by omega)
  obtain ⟨e1, e2⟩ := rec_val (M0 := s.mem) h40 hj (by omega) huk hv0 hq hr
  refine ⟨L', b', hEv, hFp, hBd, hBs, e1, ?_, ?_⟩
  · rw [Asm.limbs_upd (j := j - 1) (k := c.vl + 1) (by omega) (fun i hi hi2 => ku _ _ (by omega) (by omega)
      (by omega)), huk, e2]
  · have hc : drsC (stLen X.mem c.st) (c.vl + 1) (c.vl - c.vl / 2 + 1) ≤ drsC (c.l1 s) c.ul (c.vl - c.vl / 2 + 1) := by
      rw [hlen]; exact drsC_ul _ _ _ _ (by omega)
    have e : (j / (c.vl / 2) + 1) * c.K s = j / (c.vl / 2) * c.K s + c.K s := Nat.succ_mul _ _
    simp only [Cx.K] at e hbud ⊢
    omega

/-- the return address of the recursive call of the loop body -/
abbrev r2 : Nat := 0x1ba614

/-- **after the recursive call** (iteration `j`; `Z`/`U` = quotient/dividend at the iteration start) -/
structure A2 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 r2
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  bd : Bd c s S.mem j Z
  bs : Bs c s S.mem j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  qk : Asm.limbs S.mem c.t0 (c.vl / 2 + 1) = (c.R s j U).1
  uk : Asm.limbs S.mem c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + stackNatCost (c.l1 s) (3 * c.vl) +
    mulC (c.l1 s + StackNat.rnd (3 * c.vl)) (c.vl / 2 + 1) (c.vl / 2 - 1) ≤ bk

end FvModexp.Arm64.DivRec
