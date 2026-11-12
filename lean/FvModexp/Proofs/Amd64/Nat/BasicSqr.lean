import FvModexp.Proofs.Amd64.Nat.BasicSqrPro
import FvModexp.Proofs.Amd64.Nat.StackNat

/-!
# `basicSqr(stk, z, x)` (go-bigmodexpfix natmul.go:113), amd64: the summary (twin of `Arm64/Nat/BasicSqr.lean`)

`pro1`: entry → `CALL (*stack).nat` (large path); `full`: the `Summary` at the entry (`n < 12`: `small`; else `pro1`);
`ens`: the `Ensures` of CONVENTIONS §3; `sum`: `ens` as a callee summary. Runtime contracts: live `memclrNoHeapPointers`,
and (through `(*stack).nat`) `growslice` and `gcWriteBarrier2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.BasicSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem pro1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    (hmc : MemclrNoHeapPointersLive64 (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = st) (h3 : s.regs 3 = zp) (h1 : s.regs 1 = zl) (h7 : s.regs 7 = zc) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hce := hpre.ce; have hthA := hpre.thA; have hthV := hpre.thV; have hthO := hpre.thO
  have hzl := hpre.zl2; have hzc40 := hpre.zcb; have hzc := hpre.zlc
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hstok := hpre.stok
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hstok
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have eA : thrA = 11841176 := rfl
  rw [eA] at hthA hthV hthO
  simp only [win, outside_cons, outside_nil, and_true] at hthO
  have eD : segAddr LibBasicSqr.program (fn ++ ".deferwrap1") = 6232320 := by decide
  have hxx : BitVec.ofNat 64 (2 * xl.toNat) = xl + xl := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; omega
  have hstacc8 : s.mem.accessible (st.toNat + 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hstacc (by omega) (by omega))
  janus64_run [hthV, BitVec.msb_eq_decide, hstacc8] until [callNat]
  refine pro2 impl hap R hSN hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hra hx15 hdf _
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?qD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?qI
  case qF => janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  case qD => rw [eD]; janus64_simp
  case qI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 89, (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 40, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 64)])
      (by janus_frame) (fun r hr => ?_) hpre.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try (rw [hxx])
  all_goals try (janus64_simp; done)
  all_goals (janus64_simp; try omega)

set_option maxRecDepth 20000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) :
    Summary (LibBasicSqr.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = st ∧ s.regs 3 = zp ∧ s.regs 1 = zl ∧ s.regs 7 = zc ∧ s.regs 6 = xp ∧ s.regs 8 = xl ∧
        s.regs 9 = xc ∧ Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s)
      (fun s s' => RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  by_cases hsm : xl.toNat < 12
  · exact small impl hap R hmc b L st zp zl zc xp xl xc s hpc hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre hsm
  have c1 : CodeIn64 ((Extracted.program.onlySegments [lshVUfn]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have c2 : CodeIn64 ((Extracted.program.onlySegments [addVVfn]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have c3 : CodeIn64 ((Extracted.program.onlySegments [addMulVVWWfn]).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have c4 : CodeIn64 (Extracted.program.ofImpl impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibBasicSqr.names
  exact pro1 impl hap R (StackNat.hypL impl hap R hgr hmc hwb) (MemclrNoHeapPointersLive64.of_codeIn c4 hmc)
    (fun b L => LshVUHyp.live (Summary.of_codeIn64 c1 (lshVUHyp impl hap)) R b L)
    (fun b L => AddVVHyp.live (Summary.of_codeIn64 c2 (addVVHyp impl hap)) R b L)
    (fun b L => AddMulVVWWHyp.live (Summary.of_codeIn64 c3 (addMulVVWWHyp impl hap)) R b L)
    b L st zp zl zc xp xl xc s hpc hra hx15 hdf h0 h3 h1 h7 h6 h8 h9 hpre (by omega)

/-- **`basicSqr`** (amd64): `basicSqr(stk, z, x)` stores `x²` in `z[0:2n]`, restores the stack's `len`; writes only
`z[0:2n]`, the stack header and its free part, and the window; `fsBase` and `DF` kept; no panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [st, zp, zl, zc, xp, xl, xc]
      (Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat)
      (Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat) := by
  rw [show names = LibBasicSqr.names from rfl, ← LibBasicSqr.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hgr hmc hwb b L st zp zl zc xp xl xc) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5,
      h_a6, hpre⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hgr hmc hwb b L st zp zl zc xp xl xc)
    (A64.noExit_restrict64 hap names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.BasicSqr
