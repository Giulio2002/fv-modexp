import FvModexp.Proofs.Amd64.NatQ.MulLoopHead
import FvModexp.Proofs.Amd64.NatQ.MulNorm
import FvModexp.Proofs.Amd64.Nat.Restore
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopEnd.lean — TIGHT COSTS] `nat.mul` (amd64), chunk loop: the exit (`m ≤ i`) — `z.norm()`, the deferred `stk.restore`, the return

`mdsum`: `nat.mul.deferwrap2` (the `stk.restore(len)` closure) as a callee of `LibMul` (as `KSqrEnd.kdsum`).
`mRestPre`: its precondition at the entry (`CALL AX` at `0x5f0e61`, return `0x5f0e63` at `RSP - 264`, `DX = RSP - 64`).
`lend_fin`: the facts `post_of` needs at the return.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep)

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore` closure of `nat.mul` as a callee of `LibMul` -/
theorem mdsum (impl : List Amd64.Segment) :
    Summary (LibMul.program.link impl) (segAddr LibMul.program fnD2) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnD2, reduceSegAddr] at hpc
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

theorem mdsum_entry : segAddr LibMul.program fnD2 = mDfn := by decide

set_option maxRecDepth 20000 in
/-- the closure's precondition at its entry (memory = `A` + the defer-bit / result stores + the return address) -/
theorem mRestPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {A : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent A) (S2 : State)
    (hsp : (S2.regs 4).toNat = (s.regs 4).toNat - 264) (h2 : (S2.regs 2).toNat = (s.regs 4).toNat - 64)
    (hF : MemFrame A S2.mem [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168),
      ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80), ((s.regs 4).toNat - 264, (s.regs 4).toNat - 256)])
    (hra : S2.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0e63) : Restore.Pre S2 := by
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, -⟩ := h.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 88) true = true := by
    have := h.core.pre.1.2.1.2.2; simp only [regSP] at this; exact this
  have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  obtain ⟨hst8, -, hstacc, hst48, -, hslc, -⟩ := h.sok
  have hsl := h.slen
  have hrd : ∀ x m, (x + m ≤ (s.regs 4).toNat - 170 ∨ (s.regs 4).toNat - 168 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 80 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 264 ∨ (s.regs 4).toNat - 256 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 h3 => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((s.regs 4).toNat - 64 + 8) 8 = st := by
    rw [hrd _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 64 + 8 = (s.regs 4).toNat - 56 by omega]
    exact h.dst
  have hdln : S2.mem.readLE ((s.regs 4).toNat - 64 + 16) 8 = stLen M st := by
    rw [hrd _ _ (by omega) (by omega) (by omega), show (s.regs 4).toNat - 64 + 16 = (s.regs 4).toNat - 48 by omega]
    exact h.dln
  have hcap : S2.mem.readLE (st + 16) 8 = stCap A st := hrd _ _ (by omega) (by omega) (by omega)
  have hacc : ∀ a k w, S2.mem.accessible a k w = A.accessible a k w := fun a k w => hF.accessible a k w
  unfold Restore.Pre StackWritable
  simp only [regSP]
  rw [hsp, h2, hdst, hdln, hcap, hra]
  simp only [hacc]
  refine ⟨⟨by omega, by omega, ?_⟩, by omega, by decide, by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  · rw [h.frE.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hw0 (Or.inl rfl) (by omega) (by omega)
  · exact hstacc
  · simp only [stLen, stCap] at hsl hslc ⊢; omega
  · unfold Apart; omega
  · unfold Apart; omega

set_option maxRecDepth 20000 in
/-- **the facts `post_of` needs at the return** (memory `F` = `A` + our stores + the closure's frame + `len` restored) -/
theorem lend_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {A : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent A) {F : Memory}
    (hF : MemFrame A F [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168), ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80),
      ((s.regs 4).toNat - 272, (s.regs 4).toNat - 256), (st + 8, st + 16)])
    (hlen : F.readLE (st + 8) 8 = stLen M st) :
    stCap F st = stCap A st ∧ Outside p (8 * (xl + yl)) [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168),
      ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80), ((s.regs 4).toNat - 272, (s.regs 4).toNat - 256), (st + 8, st + 16)] ∧
      R.inv bk Lk (s.regs 14).toNat (view R.rt Lk F) ∧
      StackBackL R L1 Lk st M F ∧ MemFrame M F (R.rt ++ win s W 88 ++ (p, p + 8 * (xl + yl)) :: stkWs M st) ∧
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
  have hrd : ∀ x m, Outside x m [((s.regs 4).toNat - 170, (s.regs 4).toNat - 168),
      ((s.regs 4).toNat - 104, (s.regs 4).toNat - 80), ((s.regs 4).toNat - 272, (s.regs 4).toNat - 256),
      (st + 8, st + 16)] → F.readLE x m = A.readLE x m :=
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
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · refine LiveFrame.trans h.lf ⟨fun x m hin hz => hF.readLE x m ?_⟩ fun _ _ h => h
    have := outside_of_liveSep hin hLs
    simp only [win, stkWs, outside_cons, outside_nil, and_true] at this hz ⊢
    omega

end FvModexp.Amd64.Q.NatMul
