import FvModexp.Proofs.Arm64.Int.IntASDefs
import FvModexp.Proofs.Common.DivmcMem

/-!
# `(*Int).Add` / `(*Int).Sub` (arm64): the state after the `nat.add` / `nat.sub` call, the write barrier call and the
postcondition (pure)

`AtRet`: the facts at the return of the `nat` call (three call sites). `wbCall`: a call of `gcWriteBarrier2` in
continuation form. `post_of`: from the memory after the header stores `z.abs = (p', l', c')` (with or without the
barrier's buffer stores) and the final `z.neg` byte, the postcondition `Post`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

/-- the state at the return of the `nat.add` / `nat.sub` call: result `(p', l', c')` holding `V`, final sign byte `nb`
(before the `len > 0` test) with `±V` the signed result; `cost` the callee's budget -/
structure AtRet (sub : Bool) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State)
    (nb V cost p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State) : Prop where
  pre : Pre R b L z x y s
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  sp : S.sp = s.sp - 96#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 104#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 p'
  p64 : p' < 2 ^ 64
  r1 : S.regs 1 = BitVec.ofNat 64 l'
  r2 : S.regs 2 = BitVec.ofNat 64 c'
  fp : S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat
  lr : S.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat
  zs : S.mem.readLE (s.sp.toNat + 8) 8 = z
  ng : S.mem.readLE (s.sp.toNat - 9) 1 = hNeg s.mem x
  val : natVal S.mem p' l' = V
  norm : NatNorm S.mem p' l'
  lc : l' ≤ c'
  c40 : c' < 2 ^ 40
  lmx : l' ≤ max (hL s.mem x) (hL s.mem y) + 1
  ext : LiveExt R L L1
  bud : b - cost ≤ b1
  costle : cost ≤ asCost (hL s.mem x) (hL s.mem y)
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S.mem)
  live : NatLive S.mem R L1 p' c'
  orf : (p' = hP s.mem z ∧ c' = hC s.mem z) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)
  reuse : asNeed (hL s.mem x) (hL s.mem y) ≤ hC s.mem z → p' = hP s.mem z ∧ c' = hC s.mem z
  mf : MemFrame s.mem S.mem (R.rt ++ winA s 4560 32 ++ [(hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))])
  lf : LiveFrame s.mem S.mem L [(hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))]
  nb1 : nb ≤ 1
  res : (if nb = 0 ∨ V = 0 then (V : Int) else -(V : Int)) = resZ sub (intZ s.mem x) (intZ s.mem y)

/-- a call of `gcWriteBarrier2` (live contract) at its entry, continuation form over the contract's return state -/
theorem wbCall {p : Program} {R : RtInv} (hwb : WbLiveContract p (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {L1 : List (Nat × Nat)} {b1 : Nat} {S : State} {ret : BitVec 64} {Q : State → Prop}
    (hpc : S.pc = BitVec.ofNat 64 (cA "runtime.gcWriteBarrier2")) (hcall : CallOK S 4096 0)
    (hok : R.ok (cA "runtime.gcWriteBarrier2") [2]) (hinv : R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 S.mem))
    (hLW : LiveSep L1 [(S.sp.toNat - 4096, S.sp.toNat - 8)]) (hWR : LiveSep [(S.sp.toNat - 4096, S.sp.toNat - 8)] R.rt)
    (K : ∀ (buf : BitVec 64) (junk : Nat → BitVec 64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
      (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      MemFrame S.mem m (R.rt ++ [(S.sp.toNat - 4096, S.sp.toNat - 8)]) → LiveFrame S.mem m L1 [] →
      WbSlots R.rt m buf.toNat 2 → ApartAll buf.toNat (8 * 2) L1 →
      ApartAll buf.toNat (8 * 2) [(S.sp.toNat - 4096, S.sp.toNat - 8)] →
      InvSlots R b1 L1 (S.regs 28).toNat R.rt m buf.toNat 2 →
      ReachesRet p ret (wbRetX S junk buf f v m ex ep) Q) :
    ReachesRet p ret S Q := by
  refine ReachesRet.call (hwb L1 b1) hpc ⟨hcall, hok, hinv, hLW, hWR⟩ fun S2 _ hq => ?_
  obtain ⟨buf, junk, f, v, m, ex, ep, rfl, hfr, hlf, hsl, hapL, hapW, hinvS⟩ := hq
  exact K buf junk f v m ex ep hfr hlf hsl hapL hapW hinvS

/-- the result array is apart from `z`'s header and either live or outside `R.rt` and the window -/
theorem AtRet.arr {sub : Bool} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s : State}
    {nb V cost p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) (hc : 0 < c') :
    Apart p' (8 * c') z 32 ∧ (InRanges p' (8 * c') L1 ∨ (Outside p' (8 * c') R.rt ∧
      Outside p' (8 * c') (win s 4560 32))) := by
  have hpre := h.pre
  obtain ⟨-, -, -, -, -, -, -, -, hzH, -, -, -, -, -, -, hzo, hz0, -, -, -⟩ := hpre
  rcases h.orf with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · refine ⟨(hz0 hc).2.1, ?_⟩
    rcases (h.live hc).2.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1, hzo⟩
  · refine ⟨?_, ?_⟩
    · rcases hzH with h1 | h1
      · have := hap.apart_of_inRanges h1; unfold Apart; omega
      · exact (hin.apart h1).symm
    · rcases (h.live hc).2.1 with h1 | h1
      · exact Or.inl h1
      · obtain ⟨r, hr, a1, a2⟩ := hin
        have := MemFrame.outside_mem h1 hr
        omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the postcondition from the memory `Mw` after the header stores `len, cap` and (barrier on) the buffer stores, and the
final stores `z.abs.ptr = p'`, `z.neg = nbF` -/
theorem post_of {sub : Bool} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s : State}
    {nb V cost p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) {Mw : Memory}
    (hMw : MemFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') Mw
      (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat - 104)]))
    (hLw : LiveFrame ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') Mw L1 [])
    (hIw : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 Mw))
    (s' : State) (h0 : s'.regs 0 = BitVec.ofNat 64 z) (nbF : Nat) (hnbF : nbF = if l' = 0 then 0 else nb)
    (hm : s'.mem = (Mw.writeLE (z + 8) 8 p').writeLE z 1 nbF) :
    Post sub R b L z x y s s' := by
  have hpre := h.pre
  obtain ⟨hce, -, -, -, -, hza, hz48, hzo, hzH, -, -, -, -, hzc, -, -, -, -, -, -⟩ := hpre
  have hsp0 : 4560 ≤ s.sp.toNat := hce.2.1.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  have hc40 := h.c40; have hlc := h.lc; have hp64 := h.p64; have hnb1 := h.nb1
  have hnbF1 : nbF ≤ 1 := by rw [hnbF]; split <;> omega
  -- reads of `Mw` inside `z`'s header
  have rdW : ∀ a n, z ≤ a → a + n ≤ z + 32 →
      Mw.readLE a n = ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE a n := by
    intro a n h1 h2
    rcases hzH1 with hi | ho
    · exact hLw.readLE_nil a n (hi.sub h1 h2)
    · exact hMw.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.of_sub h1 h2, by omega⟩)
  -- reads of `Mw` inside the result array
  have rdA : 0 < c' → ∀ a n, p' ≤ a → a + n ≤ p' + 8 * c' → Mw.readLE a n = S.mem.readLE a n := by
    intro hc a n h1 h2
    obtain ⟨hap, hor⟩ := h.arr hc
    unfold Apart at hap
    rw [show Mw.readLE a n = ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c').readLE a n from ?_,
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rcases hor with hi | ⟨ho, hw⟩
    · exact hLw.readLE_nil a n (hi.sub h1 h2)
    · simp only [win, outside_cons, outside_nil, and_true] at hw
      exact hMw.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.of_sub h1 h2, by omega⟩)
  have eN : s'.mem.readLE z 1 = nbF := by
    rw [hm, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  have eP : s'.mem.readLE (z + 8) 8 = p' := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eL : s'.mem.readLE (z + 16) 8 = l' := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eC : s'.mem.readLE (z + 24) 8 = c' := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  -- reads of the final memory inside the result array
  have rdF : 0 < c' → ∀ a n, p' ≤ a → a + n ≤ p' + 8 * c' → s'.mem.readLE a n = S.mem.readLE a n := by
    intro hc a n h1 h2
    have hap := (h.arr hc).1
    unfold Apart at hap
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact rdA hc a n h1 h2
  have eV : natVal s'.mem p' l' = V := by
    rw [← h.val]
    rcases Nat.eq_zero_or_pos l' with h0 | h0
    · subst h0; rfl
    · exact rdF (by omega) _ _ (Nat.le_refl _) (by omega)
  have eNorm : NatNorm s'.mem p' l' := by
    rcases h.norm with h1 | h1
    · exact Or.inl h1
    · rcases Nat.eq_zero_or_pos l' with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rw [rdF (by omega) _ _ (by omega) (by omega)]; exact h1)
  have hacc : ∀ a n w, s'.mem.accessible a n w = S.mem.accessible a n w := by
    intro a n w
    rw [hm, Memory.accessible_writeLE, Memory.accessible_writeLE, hMw.accessible, Memory.accessible_writeLE,
      Memory.accessible_writeLE]
  -- frames
  have hFH : MemFrame S.mem ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c') [(z, z + 32)] := by janus_frame
  have hF2 : MemFrame Mw ((Mw.writeLE (z + 8) 8 p').writeLE z 1 nbF) [(z, z + 32)] := by janus_frame
  rw [← hm] at hF2
  refine ⟨h0, ?_, by simp only [hNeg]; rw [eN]; exact hnbF1, ?_, ?_, ?_, ?_, ?_, ⟨L1, b1, h.ext, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have ei : intZ s'.mem z = if nbF = 0 then (V : Int) else -(V : Int) := by
      unfold intZ; simp only [hNeg, hP, hL]; rw [eN, eP, eL, eV]
    rw [ei, ← h.res, hnbF]
    rcases Nat.eq_zero_or_pos l' with h0 | h0
    · have hV : V = 0 := by rw [← h.val, h0]; rfl
      subst hV; simp [h0]
    · have hl0 : l' ≠ 0 := by omega
      simp only [hl0, if_false]
      by_cases hn0 : nb = 0
      · simp [hn0]
      · by_cases hv0 : V = 0
        · subst hv0; simp
        · simp [hn0, hv0]
  · simp only [hNeg, hL]; rw [eN, eL, hnbF]; split <;> omega
  · simp only [hP, hL]; rw [eP, eL]; exact eNorm
  · simp only [hL, hC]; rw [eL, eC]; exact hlc
  · simp only [hL]; rw [eL]; exact h.lmx
  · simp only [hC]; rw [eC]; exact hc40
  · have := h.costle; have := h.bud; omega
  · rw [hm, view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega))]
    exact hIw
  · simp only [hP, hC]; rw [eP, eC]
    intro hc
    obtain ⟨a1, a2, a3, a4⟩ := h.live hc
    exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · simp only [hP, hC]; rw [eP, eC]; exact h.orf
  · simp only [hP, hC]; rw [eP, eC]; exact h.reuse
  · refine MemFrame.trans (rs'' := R.rt ++ winA s 4560 32 ++ [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))])
      (MemFrame.trans (rs'' := R.rt ++ winA s 4560 32 ++ [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))])
        (MemFrame.trans (rs'' := R.rt ++ winA s 4560 32 ++ [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))])
          h.mf hFH ?_) hMw ?_) hF2 ?_
    · intro a n ho
      simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨⟨ho.1.1, ho.1.2.1, ho.1.2.2⟩, ho.2.2⟩, ho.2.1⟩
    · intro a n ho
      simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨ho, ho.1.1, by omega⟩
    · intro a n ho
      simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨ho, ho.2.1⟩
  · have l1 : LiveFrame s.mem S.mem L [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))] :=
      LiveFrame.mono_ws h.lf fun a n ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.2
    refine (((l1.trans ⟨fun a n _ ho => hFH.readLE a n (by
        simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.1)⟩ fun _ _ hi => hi).trans
      (L' := L1) ⟨fun a n hi _ => hLw.readLE_nil a n hi⟩ fun _ _ hi => h.ext.inRanges_old hi).trans
      ⟨fun a n _ ho => hF2.readLE a n (by simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.1)⟩
      fun _ _ hi => hi)

/-- the final sign byte: `(len ≠ 0) & neg` -/
theorem nbF_eq (l' nb : Nat) (h : nb ≤ 1) :
    ((if l' = 0 then 0#64 else 1#64).toNat &&& nb) = if l' = 0 then 0 else nb := by
  rcases (by omega : nb = 0 ∨ nb = 1) with rfl | rfl <;> by_cases hl : l' = 0 <;> simp [hl]

/-- the live set after a call keeps the window free -/
theorem liveSep_ext {R : RtInv} {L L1 : List (Nat × Nat)} (h : LiveExt R L L1) {w : List (Nat × Nat)}
    (hL : LiveSep L w) (hw : LiveSep w R.rt) : LiveSep L1 w := by
  obtain ⟨ns, rfl, hn, -⟩ := h
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hL r hr
  · obtain ⟨hin, -⟩ := hn r hr
    refine outside_of_forall fun q hq => ?_
    have := (hw q hq)
    obtain ⟨t, ht, t1, t2⟩ := hin
    have := MemFrame.outside_mem this ht
    omega

/-- the invariant after the header stores `len, cap` -/
theorem inv_hdr {sub : Bool} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s : State}
    {nb V cost p' l' c' b1 : Nat} {L1 : List (Nat × Nat)} {S : State}
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) :
    R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 ((S.mem.writeLE (z + 16) 8 l').writeLE (z + 24) 8 c')) := by
  have hzH1 : Held R L1 z 32 := h.ext.held h.pre.2.2.2.2.2.2.2.2.1
  rw [view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega))]
  exact h.inv

/-- the final sign byte after `neg = !neg`: `(len ≠ 0) & (neg ^ 1)` -/
theorem nbF_eqC (l' nx : Nat) (h : nx ≤ 1) :
    ((if l' = 0 then 0#64 else 1#64).toNat &&& (nx ^^^ 1)) =
      if l' = 0 then 0 else 1 - nx := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> by_cases hl : l' = 0 <;> simp [hl]

end FvModexp.Arm64.IntAS
