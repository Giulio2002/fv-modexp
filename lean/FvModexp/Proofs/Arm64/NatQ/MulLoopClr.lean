import FvModexp.Proofs.Arm64.NatQ.MulLoopPA
import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.DivmcMem

/-!
# [Q-form copy of Arm64/Nat/MulLoopClr.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), the chunk loop's prologue: `clear(z[2n:])` and the defer record (natmul.go:53-54), `KA → LP`

`lpOf` (pure): `LP` at `(*stack).nat`'s entry from `KA` (at `0x1bb054`), `memclrNoHeapPointers(p + 16n, 8(m - n))`'s
post (memory `w`) and the stores of the defer bits / record (memory `P`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep
  stackBack_keep')

/-- `StackBackL` composes with a callee that kept the stack's array in the L form -/
theorem sbl_trans {R : RtInv} {L1 Lk Lk2 : List (Nat × Nat)} {st : Nat} {M A B : Memory}
    (h1 : StackBackL R L1 Lk st M A) (h2 : StackBackL R Lk Lk2 st A B) (he1 : LiveExt R L1 Lk)
    (he : LiveExt R Lk Lk2) :
    StackBackL R L1 Lk2 st M B := by
  obtain ⟨⟨-, hl1, ha1⟩, hm1⟩ := h1
  obtain ⟨⟨hok2, hl2, ha2⟩, hm2⟩ := h2
  refine ⟨⟨hok2, by rw [hl2, hl1], ?_⟩, ArrIn.trans hm1 hm2 he⟩
  rcases ha2 with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]; exact ha1
  · exact Or.inr ⟨hin, fun r hr => hap r (he1.mem_old hr)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`LP` from `KA`**, the `memclr` post (memory `w`) and the defer stores (memory `P.mem`) -/
theorem lpOf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} {S : State}
    (h : KA R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk S) {w : Memory}
    (hFc : MemFrame S.mem w (R.rt ++ [(s.sp.toNat - 256 - 4096, s.sp.toNat - 256 - 8),
      (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 24)] ++ [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))]))
    (hLFc : LiveFrame S.mem w Lk [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))])
    (hinvw : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk w))
    (hz : Mem.Zeroed w (p + 8 * (2 * yl)) (8 * (xl - yl))) (hregw : w.regions = S.mem.regions)
    (P : State) (hFs : MemFrame w P.mem [(s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 64, s.sp.toNat - 40),
      (s.sp.toNat - 16, s.sp.toNat - 8)]) (hregP : P.mem.regions = w.regions)
    (hpc : P.pc = BitVec.ofNat 64 stkNatM) (hsp : P.sp = s.sp - 256#64) (hg : P.regs 28 = s.regs 28)
    (hfp : P.regs 29 = s.sp - 264#64) (h18 : P.regs 18 = s.regs 18) (r0 : P.regs 0 = BitVec.ofNat 64 st)
    (r1 : P.regs 1 = BitVec.ofNat 64 (2 * yl)) (r30 : P.regs 30 = BitVec.ofNat 64 0x1bb0c0)
    (q94 : P.mem.readLE (s.sp.toNat - 162) 1 = 2) (q95 : P.mem.readLE (s.sp.toNat - 161) 1 = 2)
    (qdfn : P.mem.readLE (s.sp.toNat - 64) 8 = mDfn) (qdst : P.mem.readLE (s.sp.toNat - 56) 8 = st)
    (qdln : P.mem.readLE (s.sp.toNat - 48) 8 = w.readLE (st + 8) 8)
    (qdpt : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 64) :
    LP R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P := by
  have hq := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, hc40, hpw, hx12, hy12, -⟩ := hq.lay
  have h40 := hq.h40; have hlt := hq.hlt
  have hko := hq.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only at hko
  have hpst := hq.core.pst (by omega)
  unfold Apart at hpst
  simp only [win, outside_cons, outside_nil, and_true] at hpw
  have hcls : LCls R L1 M st p (xl + yl) [(p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
  obtain ⟨hfr1, hlf1⟩ := hq.frames (k := 4096) (a := 24) (by omega) (by omega) hcls hFc hLFc
  have hFsW : MemFrame w P.mem (winA s W 88) := hFs.mono fun a n ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hLs := hq.wsep
  -- the combined frame from `S.mem`
  have hFall : MemFrame S.mem P.mem (R.rt ++ [(s.sp.toNat - 256 - 4096, s.sp.toNat - 256 - 8),
      (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 24), (p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl)),
      (s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 64, s.sp.toNat - 40), (s.sp.toNat - 16, s.sp.toNat - 8)]) :=
    hFc.trans hFs fun x m ho => by
      rw [outside_append] at ho
      obtain ⟨hr, hw⟩ := ho
      simp only [outside_cons, outside_nil, and_true] at hw
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨⟨hr, by omega, by omega⟩, by omega⟩, by omega, by omega, by omega⟩
  have hLall : LiveFrame S.mem P.mem Lk [(s.sp.toNat - 256 - 4096, s.sp.toNat - 256 - 8),
      (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 24), (p + 8 * (2 * yl), p + 8 * (2 * yl) + 8 * (xl - yl)),
      (s.sp.toNat - 162, s.sp.toNat - 160), (s.sp.toNat - 64, s.sp.toNat - 40), (s.sp.toNat - 16, s.sp.toNat - 8)] :=
    ⟨fun a n hin ho => by
      simp only [outside_cons, outside_nil, and_true] at ho
      rw [hFs.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hLFc.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
  have hsbC : StackBackL R Lk Lk st S.mem P.mem ∧ stCap P.mem st = stCap S.mem st :=
    NatSqr.stackBack_keepC hq.sok hFall hLall (by simp only [outside_cons, outside_nil, and_true]; omega) (LiveExt.refl R Lk)
  have hrd : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat + 88 → (x + m ≤ s.sp.toNat - 162 ∨ s.sp.toNat - 160 ≤ x) →
      (x + m ≤ s.sp.toNat - 64 ∨ s.sp.toNat - 40 ≤ x) → (x + m ≤ s.sp.toNat - 16 ∨ s.sp.toNat - 8 ≤ x) →
      (x + m ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 232 ≤ x) → P.mem.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 h3 h4 h5 h6 => hFall.readLE _ _ (by
      rw [outside_append]
      exact ⟨hout.of_sub (by omega) (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩)
  have hsb := hsbC.1
  -- the value
  have hpH : Held R Lk p (8 * (2 * yl)) := by
    rcases hq.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := hq.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact hq.ext.held (hq.core.ext.held ((hzl (by omega)).2.1.sub (Nat.le_refl _) (by omega)))
    · exact hq.ext.held (Or.inl (hin1.sub (Nat.le_refl _) (by omega)))
  have v1 : natVal P.mem p (2 * yl) = natVal S.mem p (2 * yl) := by
    unfold natVal
    exact Held.readLE hpH hFall hLall (by simp only [outside_cons, outside_nil, and_true]; omega)
  have v2 : natVal P.mem (p + 8 * (2 * yl)) (xl - yl) = 0 := by
    unfold natVal
    rw [hFs.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact FvModexp.readLE_of_zeroed hz _ _ (Nat.le_refl _) (Nat.le_refl _)
  have e := natVal_add P.mem p (2 * yl) (xl - yl)
  rw [show 2 * yl + (xl - yl) = xl + yl by omega, v1, v2, h.val] at e
  have hlenP : stLen P.mem st = stLen M st := by rw [hsb.1.2.1, hq.sb.1.2.1]
  have hdln : w.readLE (st + 8) 8 = stLen M st := by
    rw [← hlenP]; show w.readLE (st + 8) 8 = P.mem.readLE (st + 8) 8
    exact (hFs.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)).symm
  refine ⟨?_, hpc, hsp, hg, hfp, h18, r0, r1, r30, q94, q95, qdfn, qdst, by rw [qdln, hdln], qdpt,
    by rw [e]; simp⟩
  exact
    { core := hq.core, h40 := h40, hlt := hlt, ext := hq.ext, bud := by rw [stkR_congr hsbC.2]; exact hq.bud, spk := hq.spk,
      inv := inv_frame_winA hFsW hout (by omega) (by decide) hinvw, reg := hregP.trans (hregw.trans hq.reg),
      fr := hfr1.trans hFsW fun x m ho => ⟨ho, by simp only [outside_append] at ho; exact ho.1.2⟩,
      lf := LiveFrame.trans hlf1 (lf_win' _ hFsW hLs) fun _ _ h => h,
      sok := hsb.1.1, sb := sbl_trans hq.sb hsb hq.ext (LiveExt.refl R Lk),
      lr := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.lr,
      fp := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.fp,
      c96 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.c96,
      n120 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.n120,
      n136 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.n136,
      p144 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.p144,
      s184 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.s184,
      a296 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.a296,
      a304 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.a304,
      a312 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.a312,
      a320 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.a320,
      a328 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.a328,
      a336 := (hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hq.a336,
      px := hq.px, py := hq.py }

end FvModexp.Arm64.Q.NatMul
