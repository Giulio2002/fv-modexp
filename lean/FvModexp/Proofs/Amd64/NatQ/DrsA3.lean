import FvModexp.Proofs.Amd64.NatQ.DrsA2

set_option autoImplicit false

/-! (amd64 twin (asm s47) of Arm64/NatQ/DrsA3.lean)
# `divRecursiveStep` (amd64), loop body segment 3: relations (pure)

`qhat = qhat.norm()` (natdiv.go:828), `mark := stk.save()`, `qhatv := stk.nat(3n)`, `clear(qhatv)` (natdiv.go:829-830).

* `Rg R c s Lk M a n`: a range of the stack's array, separated like the free part (`Fp`).
* `Ev.callG` / `Fp.grow`: the environment and the free part after a callee that GROWS the stack (`stk.nat`).
* `Q3 c s M qn`: the slots `len(qhat.norm())` (`r-200`) and `mark` (`r-160`); `V3 c s M qv`: `qhatv` (`r-72`, `r-256`, `r-240`).
* `N3`: the state at `CALL (*stack).nat(3n)` (`0x5efc93`); `A3`: after `clear(qhatv)` (`0x5efcc5`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- a range of the stack's array, separated from everything the body uses -/
structure Rg (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (a n : Nat) : Prop where
  h : Held R Lk a n
  w : Outside a n (win s c.W 96)
  g : Apart a n (grd s) 8
  fs : Apart a n (tls s) 8
  st : Apart c.st 24 a n
  gA : Apart a n RunIface.gA 32
  q : Apart a n c.qp (8 * c.ql)
  u : Apart a n c.up (8 * c.ul)
  v : Apart a n c.vp (8 * c.vl)
  t0 : Apart a n c.t0 (8 * (c.vl / 2 + 1))

/-- the stack's array from the length `l1` (after `qhat0`) on: the part `stk.restore(mark)` frees again -/
@[reducible] def FL (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (M : Memory) : Prop :=
  Rg R c s Lk (stW M c.st + 8 * c.l1 s) (8 * (stCap M c.st - c.l1 s))

/-- `FL` with the stack header unchanged -/
theorem FL.hdr {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {M M' : Memory} (h : FL R c s Lk M)
    (eW : stW M' c.st = stW M c.st) (eC : stCap M' c.st = stCap M c.st) : FL R c s Lk M' := by
  unfold FL; rw [eW, eC]; exact h

/-- `FL` across own stores (reads outside the own window kept) -/
theorem FL.own {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {M M' : Memory}
    (hcr : Cr R c s) (h : FL R c s Lk M)
    (rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n) : FL R c s Lk M' := by
  have hsto : Outside c.st 24 (win s c.W 96) := hcr.pre.sti.2.1
  have eW : stW M' c.st = stW M c.st := rd _ _ (hsto.of_sub (by omega) (by omega))
  have eC : stCap M' c.st = stCap M c.st := rd _ _ (hsto.of_sub (by omega) (by omega))
  exact h.hdr eW eC

/-- a sub-range of the free part -/
theorem Fp.rg {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {M : Memory} {lM a n : Nat}
    (h : Fp R c s Lk M lM) (h1 : stW M c.st + 8 * lM ≤ a) (h2 : a + n ≤ stW M c.st + 8 * stCap M c.st) :
    Rg R c s Lk a n := by
  have hs : stW M c.st + 8 * lM + 8 * (stCap M c.st - lM) ≥ a + n := by omega
  exact ⟨h.fh.sub h1 (by omega), h.fw.of_sub h1 (by omega), apL h.fg h1 (by omega), apL h.ffs h1 (by omega), apR h.fst h1 (by omega),
    apL h.fgA h1 (by omega), apL h.fq h1 (by omega), apL h.fu h1 (by omega), apL h.fv h1 (by omega),
    apL h.ft0 h1 (by omega)⟩

set_option maxHeartbeats 8000000 in
/-- **the environment after a stack-growing callee** (frame `R.rt ++ wsS ++ ws ++ stkWs M st`) -/
theorem Ev.callG {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {bk b' : Nat} {M M' : Memory}
    {wsS ws : List (Nat × Nat)} (hcr : Cr R c s) (h : Ev R c s Lk bk M) (hl : stLen s.mem c.st ≤ stLen M c.st)
    (hF : MemFrame M M' (R.rt ++ wsS ++ ws ++ stkWs M c.st)) (hL : LiveFrame M M' Lk (ws ++ stkWs M c.st))
    (hS : ∀ x k, Outside x k (win s c.W 96) → Outside x k wsS)
    (hW1 : ∀ x k, Outside x k (R.rt ++ win s c.W 96 ++ c.ws s) → Outside x k ws)
    (hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k ws)
    (hx : LiveExt R Lk L') (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M')) (hok : StkOK M' R L' c.st)
    (hsar : (stW M' c.st = stW M c.st ∧ stCap M' c.st = stCap M c.st) ∨
      (InRanges (stW M' c.st) (8 * stCap M' c.st) R.rt ∧ ApartAll (stW M' c.st) (8 * stCap M' c.st) Lk))
    (hreg : M'.regions = M.regions) (harr : ArrIn L' c.st M M') :
    Ev R c s L' b' M' := by
  have hloc := (free_loc h hl).out
  have hfr : MemFrame M M' (R.rt ++ win s c.W 96 ++ c.ws s) := hF.mono fun x k ho => by
    have h1 := hW1 x k ho
    have h2 := hloc.1 x k ho
    rw [outside_append] at ho
    obtain ⟨ho1, ho2⟩ := ho
    rw [outside_append] at ho1
    obtain ⟨hr, hw⟩ := ho1
    rw [outside_append, outside_append, outside_append]
    refine ⟨⟨⟨hr, hS x k hw⟩, h1⟩, ?_⟩
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho2 h2 ⊢
    exact ⟨by omega, by omega⟩
  refine ⟨h.ext.trans hx, by rw [hreg]; exact h.reg, hinv, mf_trans h.fr hfr, ?_, hok, ?_, h.sarrL.trans harr hx⟩
  · refine ⟨fun x k hin ho => ?_⟩
    rw [hL.readLE x k ((hcr.ext1.trans h.ext).inRanges_old hin) ?_]
    · exact h.lf.readLE x k hin ho
    · have h1 := hW2 x k hin ho
      have h2 := hloc.2 x k hin ho
      rw [outside_append]
      refine ⟨h1, ?_⟩
      simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho h2 ⊢
      exact ⟨by omega, by omega⟩
  · rcases hsar with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact h.sarr
    · exact Or.inr ⟨hin, fun r hr => hap r ((hcr.ext1.trans h.ext).mem_old hr)⟩

/-- a sub-range of an `Rg` range -/
theorem Rg.sub {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {a n a' n' : Nat} (h : Rg R c s Lk a n)
    (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Rg R c s Lk a' n' :=
  ⟨h.h.sub h1 h2, h.w.of_sub h1 h2, apL h.g h1 h2, apL h.fs h1 h2, apR h.st h1 h2, apL h.gA h1 h2, apL h.q h1 h2, apL h.u h1 h2,
    apL h.v h1 h2, apL h.t0 h1 h2⟩

set_option maxHeartbeats 8000000 in
/-- **the free part after a stack-growing callee** (`lM → lM'`), and the grown-into range `[lM, lM')` -/
theorem Fp.grow {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {lM lM' : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk M) (h : Fp R c s Lk M lM) (hle : lM ≤ lM') (hl0 : 0 < lM') (hok : StkOK M' R L' c.st) (hlen : stLen M' c.st = lM')
    (hsar : (stW M' c.st = stW M c.st ∧ stCap M' c.st = stCap M c.st) ∨
      (InRanges (stW M' c.st) (8 * stCap M' c.st) R.rt ∧ ApartAll (stW M' c.st) (8 * stCap M' c.st) Lk)) :
    Fp R c s L' M' lM' ∧ Rg R c s L' (stW M' c.st + 8 * lM) (8 * (lM' - lM)) ∧
      Rg R c s L' (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) := by
  have hlc := hok.2.2.2.2.2.1
  rw [hlen] at hlc
  have hh : Held R L' (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) := by
    obtain ⟨-, hh, -, -⟩ := hok.2.2.2.2.1 (by omega); exact hh.sub (by omega) (by omega)
  have hR : Rg R c s L' (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) := by
    rcases hsar with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
      rw [← e1, ← e2] at h3 h4 h5 h6 h7 h8 h9 h10 h11
      exact ⟨hh, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    · have hW := hcr.hW; have := drsW64_ge c.vl
      have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
      have hpre := hcr.pre
      obtain ⟨-, -, hqh, -, -⟩ := hpre.qa
      obtain ⟨-, -, huh, -, -⟩ := hpre.ua
      obtain ⟨-, -, hvh, -, -, -, -⟩ := hpre.va
      obtain ⟨-, -, -, -, hout, -, hgr, -, -, -, htrt, -⟩ := hpre.ce
      have sub : ∀ {x k}, Apart x k (stW M' c.st) (8 * stCap M' c.st) →
          Apart x k (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) := fun hh => by unfold Apart at hh ⊢; omega
      have sub' : ∀ {x k}, Apart x k (stW M' c.st) (8 * stCap M' c.st) →
          Apart (stW M' c.st + 8 * lM) (8 * (stCap M' c.st - lM)) x k := fun hh => by unfold Apart at hh ⊢; omega
      have hw1 := outside_of_inRangesR hout hin
      have hg1 := outside_of_inRangesR hgr hin
      have hgA1 := outside_of_inRangesR hcr.pre.gl.2.2.2.2.2.2.2.2.1 hin
      have ht1 := outside_of_inRangesR htrt hin
      refine ⟨hh, ?_, sub' (by unfold Apart grd; omega), sub' (by unfold Apart tls; omega), sub (fresh_apart hev.sok.2.1 hin hap),
        sub' (by unfold Apart; omega), sub' ((fresh_apart (hext.held hqh) hin hap)),
        sub' ((fresh_apart (hext.held huh) hin hap)), sub' ((fresh_apart (hext.held hvh) hin hap)),
        sub' ((fresh_apart (hev.ext.held hcr.t0h) hin hap))⟩
      simp only [win, outside_cons, outside_nil, and_true]; omega
  have h2 := hR.sub (a' := stW M' c.st + 8 * lM') (n' := 8 * (stCap M' c.st - lM')) (by omega) (by omega)
  exact ⟨⟨hlen, h2.h, h2.w, h2.g, h2.fs, h2.st, h2.gA, h2.q, h2.u, h2.v, h2.t0⟩, hR.sub (by omega) (by omega), hR⟩

/-- `FL` (the array from `l1` on) survives a callee that keeps the stack length (it may grow the array) -/
theorem FL.callS {R : RtInv} {c : Cx} {s : State} {Lk L' : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk M) (h : FL R c s Lk M) (hl0 : 0 < stLen M c.st) (hl1 : c.l1 s ≤ stLen M c.st) (hx : LiveExt R Lk L')
    (hsb : StackBackL R Lk L' c.st M M') : FL R c s L' M' := by
  obtain ⟨⟨hok, hlen, hsar⟩, -⟩ := hsb
  rcases hsar with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · have h' := h.hdr e1 e2
    exact ⟨hx.held h'.h, h'.w, h'.g, h'.fs, h'.st, h'.gA, h'.q, h'.u, h'.v, h'.t0⟩
  · have hW := hcr.hW; have := drsW64_ge c.vl
    have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
    have hpre := hcr.pre
    obtain ⟨-, -, hqh, -, -⟩ := hpre.qa
    obtain ⟨-, -, huh, -, -⟩ := hpre.ua
    obtain ⟨-, -, hvh, -, -, -, -⟩ := hpre.va
    obtain ⟨-, -, -, -, hout, -, hgr, -, -, -, htrt, -⟩ := hpre.ce
    have hlc := hok.2.2.2.2.2.1
    have hl' : c.l1 s ≤ stLen M' c.st := by rw [hlen]; exact hl1
    have hl0' : 0 < stLen M' c.st := by rw [hlen]; exact hl0
    have fh : Held R L' (stW M' c.st + 8 * c.l1 s) (8 * (stCap M' c.st - c.l1 s)) := by
      obtain ⟨-, hh, -, -⟩ := hok.2.2.2.2.1 (by omega)
      exact hh.sub (by omega) (by omega)
    have sub : ∀ {x k}, Apart x k (stW M' c.st) (8 * stCap M' c.st) →
        Apart x k (stW M' c.st + 8 * c.l1 s) (8 * (stCap M' c.st - c.l1 s)) := fun hh => by unfold Apart at hh ⊢; omega
    have sub' : ∀ {x k}, Apart x k (stW M' c.st) (8 * stCap M' c.st) →
        Apart (stW M' c.st + 8 * c.l1 s) (8 * (stCap M' c.st - c.l1 s)) x k := fun hh => by unfold Apart at hh ⊢; omega
    have hw1 := outside_of_inRangesR hout hin
    have hg1 := outside_of_inRangesR hgr hin
    have hgA1 := outside_of_inRangesR hcr.pre.gl.2.2.2.2.2.2.2.2.1 hin
    have ht1 := outside_of_inRangesR htrt hin
    refine ⟨fh, ?_, sub' (by unfold Apart grd; omega), sub' (by unfold Apart tls; omega), sub (fresh_apart hev.sok.2.1 hin hap),
      sub' (by unfold Apart; omega), sub' ((fresh_apart (hext.held hqh) hin hap)),
      sub' ((fresh_apart (hext.held huh) hin hap)), sub' ((fresh_apart (hext.held hvh) hin hap)),
      sub' ((fresh_apart (hev.ext.held hcr.t0h) hin hap))⟩
    simp only [win, outside_cons, outside_nil, and_true]; omega


/-! ## slots of segment 3 -/

/-- `len(qhat.norm())` (`0xc0(SP)` = `r-200`) and `mark` (`0xe8(SP)` = `r-160`) -/
structure Q3 (c : Cx) (s : State) (M : Memory) (qn : Nat) : Prop where
  s208 : M.readLE ((s.regs 4).toNat - 200) 8 = qn
  s256 : M.readLE ((s.regs 4).toNat - 160) 8 = c.l1 s

/-- `qhatv` (`0x140(SP)` = `r-72` ptr, `0x88(SP)` = `r-256` len, `0x98(SP)` = `r-240` cap) -/
structure V3 (c : Cx) (s : State) (M : Memory) (qv : Nat) : Prop where
  s328 : M.readLE ((s.regs 4).toNat - 72) 8 = qv
  s152 : M.readLE ((s.regs 4).toNat - 256) 8 = 3 * c.vl
  s168 : M.readLE ((s.regs 4).toNat - 240) 8 = 3 * c.vl

/-- the upper part `[SP-297, SP+96)` of the own frame (scratch slots of the body) -/
@[reducible] def HiOut (s : State) (rs : List (Nat × Nat)) : Prop := Outside ((s.regs 4).toNat - 297) 393 rs

theorem Q3.frame {c : Cx} {s : State} {M M' : Memory} {qn : Nat} {rs : List (Nat × Nat)} (h : Q3 c s M qn)
    (hF : MemFrame M M' rs) (ho : HiOut s rs) (h0 : 408 ≤ (s.regs 4).toNat) : Q3 c s M' qn :=
  ⟨by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s208,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s256⟩

theorem V3.frame {c : Cx} {s : State} {M M' : Memory} {qv : Nat} {rs : List (Nat × Nat)} (h : V3 c s M qv)
    (hF : MemFrame M M' rs) (ho : HiOut s rs) (h0 : 408 ≤ (s.regs 4).toNat) : V3 c s M' qv :=
  ⟨by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s328,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s152,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s168⟩

/-- a callee frame `R.rt ++ win S k a ++ ws` (`S.sp = SP - 400`, `a ≤ 103`) avoids the upper own frame when `ws`
does -/
theorem hiOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside ((s.regs 4).toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ (s.regs 4).toNat)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 400) (ha : a ≤ 103) (hws : HiOut s ws) :
    HiOut s (R.rt ++ win S k a ++ ws) := by
  simp only [HiOut, win, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, hws⟩

theorem hiOut_win {s : State} {W x n : Nat} (h : Outside x n (win s W 96)) (hW : 408 ≤ W) (h0 : W ≤ (s.regs 4).toNat) :
    HiOut s [(x, x + n)] := by
  simp only [HiOut, win, outside_cons, outside_nil, and_true] at h ⊢; omega

/-! ## the states -/

/-- the return address of the `stk.nat(3n)` call -/
abbrev r3n : Nat := 0x5efc98

/-- **at `CALL (*stack).nat(3n)`** (`qn` = `len(qhat.norm())`) -/
structure N3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (X : State) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  pc : X.rip = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)
  sp : X.regs 4 = s.regs 4 - 400#64
  r5 : X.regs 5 = s.regs 4 - 8#64
  r14 : X.regs 14 = s.regs 14
  fs : X.fsBase = s.fsBase
  df : X.df = false
  x15 : X.xmm 15 = 0#128
  r0 : X.regs 0 = BitVec.ofNat 64 c.st
  r3 : X.regs 3 = BitVec.ofNat 64 (3 * c.vl)
  ra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = r3n
  cr : Cr R c s
  ev : Ev R c s Lk bk X.mem
  fp : Fp R c s Lk X.mem (c.l1 s)
  bd : Bd c s X.mem j Z
  bs : Bs c s X.mem j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  qk : Asm.limbs X.mem c.t0 (c.vl / 2 + 1) = (c.R s j U).1
  uk : Asm.limbs X.mem c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal X.mem c.t0 qn = natVal X.mem c.t0 (c.vl / 2 + 1)
  qN : NatNorm X.mem c.t0 qn
  q3 : Q3 c s X.mem qn
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq X.mem c.st ≤ bk

/-- the return address of `clear(qhatv)` -/
abbrev r3c : Nat := 0x5efcc5

/-- the address of `qhatv` -/
@[reducible] def Cx.qv (c : Cx) (s : State) (M : Memory) : Nat := stW M c.st + 8 * c.l1 s

/-- **after `clear(qhatv)`** (`0x5efcc5`) -/
structure A3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 r3c
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : Bd c s S.mem j Z
  bs : Bs c s S.mem j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  qk : Asm.limbs S.mem c.t0 (c.vl / 2 + 1) = (c.R s j U).1
  uk : Asm.limbs S.mem c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal S.mem c.t0 qn = natVal S.mem c.t0 (c.vl / 2 + 1)
  qN : NatNorm S.mem c.t0 qn
  q3 : Q3 c s S.mem qn
  v3 : V3 c s S.mem (c.qv s S.mem)
  rg : Rg R c s Lk (c.qv s S.mem) (8 * (3 * c.vl))
  fl : FL R c s Lk S.mem
  z0 : S.mem.readLE (c.qv s S.mem) (8 * (3 * c.vl)) = 0
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq S.mem c.st ≤ bk

end FvModexp.Amd64.Q.DivRec
