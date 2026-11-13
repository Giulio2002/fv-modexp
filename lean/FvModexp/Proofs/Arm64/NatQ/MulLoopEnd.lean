import FvModexp.Proofs.Arm64.NatQ.MulLoopHead
import FvModexp.Proofs.Arm64.NatQ.MulNorm
import FvModexp.Proofs.Arm64.NatQ.KSqrEnd

/-!
# [Q-form copy of Arm64/Nat/MulLoopEnd.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), chunk loop: the exit (`m ≤ i`) — `z.norm()`, the deferred `stk.restore`, the return

`mdsum`: `nat.mul.deferwrap2` (the `stk.restore(len)` closure) as a callee of `LibMul` (as `KSqrEnd.kdsum`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (outside_of_liveSep)

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore` closure of `nat.mul` as a callee of `LibMul` -/
theorem mdsum (impl : List Segment) :
    Summary (LibMul.program.link impl) (segAddr LibMul.program fnD2) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnD2, reduceSegAddr] at hpc
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

theorem mdsum_entry : segAddr LibMul.program fnD2 = mDfn := by decide

set_option maxRecDepth 20000 in
/-- the closure's precondition at its entry (`CALL (R0)` at `0x1bb2cc`; memory = `A` + the defer-bit / result stores) -/
theorem mRestPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {A : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent A) (S2 : State)
    (hsp : S2.sp.toNat = s.sp.toNat - 256) (hg : S2.regs 28 = s.regs 28)
    (h26 : (S2.regs 26).toNat = s.sp.toNat - 64) (h30 : S2.regs 30 = BitVec.ofNat 64 0x1bb2d0)
    (hF : MemFrame A S2.mem [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80)]) :
    Restore.Pre S2 := by
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, -⟩ := h.lay
  have hce := h.callee (S1 := { S2 with mem := A }) (stk1 := 24) (above1 := 0) hsp hg rfl (by omega) (by omega)
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal', hb', ha', hw'⟩, -⟩ := hce
  have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  obtain ⟨hst8, -, hstacc, hst48, -, hslc, -⟩ := h.sok
  have hsl := h.slen
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 162 ∨ s.sp.toNat - 160 ≤ x) →
      (x + m ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 80 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hgw : S2.mem.readLE ((s.regs 28).toNat + 16) 8 = A.readLE ((s.regs 28).toNat + 16) 8 := by
    unfold Apart at hga; exact hrd _ _ (by omega) (by omega)
  have hdst : S2.mem.readLE (s.sp.toNat - 64 + 8) 8 = st := by
    rw [hrd _ _ (by omega) (by omega), show s.sp.toNat - 64 + 8 = s.sp.toNat - 56 by omega]; exact h.dst
  have hdln : S2.mem.readLE (s.sp.toNat - 64 + 16) 8 = stLen M st := by
    rw [hrd _ _ (by omega) (by omega), show s.sp.toNat - 64 + 16 = s.sp.toNat - 48 by omega]; exact h.dln
  have hcap : S2.mem.readLE (st + 16) 8 = stCap A st := hrd _ _ (by omega) (by omega)
  have hacc : ∀ a k w, S2.mem.accessible a k w = A.accessible a k w := fun a k w => hF.accessible a k w
  have hwA : A.accessible (s.sp.toNat - W) (W + 88) true = true := by
    rw [h.frE.accessible]; exact h.core.pre.1.2.1.2.2.2
  simp only at hg1 hg2 hg3 hal' hb' ha' hw'
  rw [← hg] at hgw
  unfold Restore.Pre GuardOK
  refine ⟨⟨hg1, by rw [hacc]; exact hg2, by rw [hgw]; omega⟩, ⟨hal', hb', ha', by rw [hacc]; exact hw'⟩,
    by rw [h30]; decide, by rw [h30]; decide, by rw [h26]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h26, hacc]
    exact Memory.accessible_sub _ hwA (Or.inl rfl) (by omega) (by omega)
  · rw [h26, hdst]; omega
  · rw [h26, hdst, hacc]; exact hstacc
  · rw [h26, hdst, hdln, hcap]; simp only [stLen, stCap] at hsl hslc ⊢; omega
  · rw [h26, hdst, hsp]; unfold Apart; omega
  · rw [h26, hsp]; unfold Apart; omega

set_option maxRecDepth 20000 in
/-- **the facts `post_of` needs at the return** (memory `F` = `A` + our stores + the closure's frame + `len` restored) -/
theorem lend_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {A : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent A) {F : Memory}
    (hF : MemFrame A F [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80),
      (s.sp.toNat - 280, s.sp.toNat - 264), (st + 8, st + 16)])
    (hlen : F.readLE (st + 8) 8 = stLen M st) :
    stCap F st = stCap A st ∧ Outside p (8 * (xl + yl)) [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80),
      (s.sp.toNat - 280, s.sp.toNat - 264), (st + 8, st + 16)] ∧ R.inv bk Lk (s.regs 28).toNat (view R.rt Lk F) ∧
      StackBackL R L1 Lk st M F ∧ MemFrame M F (R.rt ++ winA s W 88 ++ (p, p + 8 * (xl + yl)) :: stkWs M st) ∧
      LiveFrame M F L1 ((p, p + 8 * (xl + yl)) :: stkWs M st) := by
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, hc40, hpw, -⟩ := h.lay
  have h40 := h.h40
  have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  have hpst := h.core.pst (by omega)
  unfold Apart at hpst
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hLs := h.wsep
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hslc, hsc40⟩ := h.sok
  have hsl := h.slen
  have hrd : ∀ x m, Outside x m [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 104, s.sp.toNat - 80),
      (s.sp.toNat - 280, s.sp.toNat - 264), (st + 8, st + 16)] → F.readLE x m = A.readLE x m :=
    fun x m hx => hF.readLE _ _ hx
  have eW : stW F st = stW A st := hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have eC : stCap F st = stCap A st := hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a k w, F.accessible a k w = A.accessible a k w := fun a k w => hF.accessible a k w
  have hlenF : stLen F st = stLen M st := hlen
  refine ⟨eC, by simp only [outside_cons, outside_nil, and_true]; omega, ?_, ?_, ?_, ?_⟩
  · refine RtInv.inv_frame' hF (fun r hr => ?_) h.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · left; exact hout.of_sub (by omega) (by omega)
    · left; exact hout.of_sub (by omega) (by omega)
    · left; exact hout.of_sub (by omega) (by omega)
    · rcases hsth.sub (a := st + 8) (n := 8) (by omega) (by omega) with h1 | h1
      · right; simpa using h1
      · left; simpa using h1
  · refine ⟨⟨⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, ?_, ?_, by rw [eC]; exact hsc40⟩, hlenF, ?_⟩,
      h.smem.congr eW eC fun _ h => h⟩
    · show NatLive F R Lk (stW F st) (stCap F st)
      rw [eW, eC]
      intro h0
      obtain ⟨a1, a2, a3, a4⟩ := hnl h0
      exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
    · show stLen F st ≤ stCap F st
      rw [hlenF, eC]; omega
    · rw [eW, eC]; exact h.sarr
  · refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · refine LiveFrame.trans h.lf ⟨fun x m hin hz => hF.readLE x m ?_⟩ fun _ _ h => h
    have := outside_of_liveSep hin hLs
    simp only [win, stkWs, outside_cons, outside_nil, and_true] at this hz ⊢
    omega

end FvModexp.Arm64.Q.NatMul
