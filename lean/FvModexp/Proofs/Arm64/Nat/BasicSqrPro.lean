import FvModexp.Proofs.Arm64.Nat.BasicSqrClr

/-!
# `basicSqr` (arm64): the large path's prologue — `defer stk.restore(stk.save())`, `t := stk.nat(2n)` (natmul.go:119-120)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.BasicSqr

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0x80

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : Nat) (s P : State) : Prop where
  pc : P.pc = BitVec.ofNat 64 callNat
  sp : P.sp = s.sp - 208#64
  r28 : P.regs 28 = s.regs 28
  r29 : P.regs 29 = s.sp - 216#64
  r18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (2 * xl)
  fr : MemFrame s.mem P.mem [(s.sp.toNat - 216, s.sp.toNat - 200), (s.sp.toNat - 89, s.sp.toNat - 88),
    (s.sp.toNat - 56, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 64)]
  reg : P.mem.regions = s.mem.regions
  lr : P.mem.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat
  fp : P.mem.readLE (s.sp.toNat - 216) 8 = (s.regs 29).toNat
  kk : P.mem.readLE (s.sp.toNat - 56) 8 = 2 * xl
  dfn : P.mem.readLE (s.sp.toNat - 40) 8 = segAddr LibBasicSqr.program (fn ++ ".deferwrap1")
  dst : P.mem.readLE (s.sp.toNat - 32) 8 = st
  dn : P.mem.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : P.mem.readLE (s.sp.toNat + 16) 8 = zp
  s2 : P.mem.readLE (s.sp.toNat + 24) 8 = zl
  s3 : P.mem.readLE (s.sp.toNat + 32) 8 = zc
  s4 : P.mem.readLE (s.sp.toNat + 40) 8 = xp
  s5 : P.mem.readLE (s.sp.toNat + 48) 8 = xl
  s6 : P.mem.readLE (s.sp.toNat + 56) 8 = xc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : ExpHyp.StackNatHyp impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (hmc : MemclrNoHeapPointersLive (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (P : State) (hP : AtNat R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s P)
    (hinvP : R.inv b L (s.regs 28).toNat (view R.rt L P.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) P fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments [ExpHyp.fnStackNat]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hSN' := fun b L => Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1)
    (noExit_restrict hap [ExpHyp.fnStackNat]) hc
  clear hc
  obtain ⟨hpc, hsp, h28, h29, h18, r0, r1, hF, hreg, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := hP
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  simp only [win, outside_cons, outside_nil, and_true] at hLs
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 64 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hPacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_win hdl hreg hro (hF.widen R.rt) hw (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega)
  have hgP : P.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hrd _ _ (by unfold Apart at hga; omega)
  have hstok := hpre.stok
  have hstO : StkOK P.mem R L st.toNat := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hstok
    simp only [StkOK, stW, stLen, stCap] at a5 a6 a7 ⊢
    rw [hrd st.toNat 8 (by omega), hrd (st.toNat + 8) 8 (by omega), hrd (st.toNat + 16) 8 (by omega), hPacc]
    refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
    intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hPacc]; exact b3, b4⟩
  janus_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13] until [callClr] calls [hSN' b L]
  trace_state
  all_goals sorry

end FvModexp.Arm64.BasicSqr
