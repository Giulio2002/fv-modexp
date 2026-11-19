import FvModexp.Proofs.Arm64.Nat.BasicSqrPro

/-!
# `basicSqr(stk, z, x)` (go-bigmodexpfix natmul.go:113), arm64: the summary

`pro1`: entry → `CALL (*stack).nat` (large path); `full`: the `Summary` at the entry (`n < 12`: `small`; else `pro1`);
`ens`: the `Ensures` of CONVENTIONS §3; `sum`: `ens` as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.BasicSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem pro1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : StackNat.HypL impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (hmc : MemclrNoHeapPointersLive (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = st) (h1 : s.regs 1 = zp)
    (h2 : s.regs 2 = zl) (h3 : s.regs 3 = zc) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hce := hpre.ce; have hthA := hpre.thA; have hthV := hpre.thV; have hthO := hpre.thO
  have hzl := hpre.zl2; have hzc40 := hpre.zcb; have hzc := hpre.zlc
  have hlen := hpre.stlen
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce'
  have hstok := hpre.stok
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hstok
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have eA : thrA = 7147152 := rfl
  rw [eA] at hthA hthV hthO
  simp only [win, outside_cons, outside_nil, and_true] at hthO
  have eD : segAddr LibBasicSqr.program (fn ++ ".deferwrap1") = 1817392 := by decide
  have hxx : BitVec.ofNat 64 (2 * xl.toNat) = xl + xl := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; omega
  janus_run [hthV, toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 12) (by decide)] until [callNat]
  refine pro2 impl hap R stkSN abSN hSN hk1 hk2 hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hl4 hl48 _
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?qD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?qI
  case qF => janus_frame
  case qR => simp only [Memory.regions_writeLE]
  case qD => rw [eD]; janus_simp
  case qI =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 216, s.sp.toNat - 200), (s.sp.toNat - 89, s.sp.toNat - 88),
      (s.sp.toNat - 56, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 64)]) (by janus_frame) (fun r hr => ?_) hpre.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try (rw [hxx])
  all_goals try (janus_simp; done)
  all_goals (janus_simp; try omega)

set_option maxRecDepth 20000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (stkSN abSN : Nat) (hSN : StackNat.HypL impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) :
    Summary (LibBasicSqr.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = st ∧ s.regs 1 = zp ∧
        s.regs 2 = zl ∧ s.regs 3 = zc ∧ s.regs 4 = xp ∧ s.regs 5 = xl ∧ s.regs 6 = xc ∧
        Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  by_cases hsm : xl.toNat < 12
  · exact small impl hap R hmc b L st zp zl zc xp xl xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre hsm
  have c1 : CodeIn ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have c2 : CodeIn ((Extracted.program.onlySegments [addVVfn]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have c3 : CodeIn ((Extracted.program.onlySegments [addMulVVWWfn]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have c4 : CodeIn (Extracted.program.ofImpl impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibBasicSqr.names
  exact pro1 impl hap R stkSN abSN hSN hk1 hk2 (MemclrNoHeapPointersLive.of_codeIn c4 hmc)
    (fun b L => LshVUHyp.live (Summary.of_codeIn c1 (lshVUHyp impl hap)) R b L)
    (fun b L => AddVVHyp.live (Summary.of_codeIn c2 (addVVHyp impl hap)) R b L)
    (fun b L => AddMulVVWWHyp.live (Summary.of_codeIn c3 (addMulVVWWHyp impl hap)) R b L)
    b L st zp zl zc xp xl xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre (by omega)

/-- **`basicSqr`** (arm64): `basicSqr(stk, z, x)` stores `x²` in `z[0:2n]`, restores the stack's `len`; writes only
`z[0:2n]`, the stack header and its free part, and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (stkSN abSN : Nat) (hSN : StackNat.HypL impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [st, zp, zl, zc, xp, xl, xc]
      (Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat)
      (Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat) := by
  janus_ensures_old [FvModexp.Arm64.BasicSqr.Pre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.BasicSqr.thrA, FvModexp.Arm64.win, FvModexp.NatLive, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Arm64.BasicSqr.freeP, FvModexp.Arm64.BasicSqr.freeN, FvModexp.stLen, FvModexp.Arm64.StackNat.wbA, Janus.Spec.GuardOK, Janus.Spec.StackOK]
  rw [show names = LibBasicSqr.names from rfl, ← LibBasicSqr.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmc stkSN abSN hSN hk1 hk2 b L st zp zl zc xp xl xc) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (stkSN abSN : Nat) (hSN : StackNat.HypL impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmc stkSN abSN hSN hk1 hk2 b L st zp zl zc xp xl xc)
    (noExit_restrict hap names) (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.BasicSqr
