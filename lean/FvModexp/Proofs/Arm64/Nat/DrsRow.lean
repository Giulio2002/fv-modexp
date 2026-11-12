import FvModexp.Proofs.Arm64.Nat.DrsStep
import FvModexp.Proofs.Arm64.Nat.NatMulXE
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites

set_option autoImplicit false

/-!
# Row: `nat.divRecursiveStep` (arm64) on the Run extraction — `DivLarge.DrsHyp` at `DivRec.drsC`

`correctness` = `DivRec.hyp` with divmc's `NatMul.hypXE` for its `nat.mul` calls (the recursion, `stk.nat`,
`addVV`/`subVW`/`cmp`/`divBasic` all proved) moved to `Extracted.program.link impl` (`Ensures.full`); window `40960`
below / `96` above `SP`. Statement: `DivLarge.DrsPre` → `DivLarge.DrsPost` (`q[0 : len q] = U / V` with `len q` words,
`u = U mod V`, the stack restored, `StackBackL`). Split out of the `nat.div` row so that each row's own modules fit
the per-row cap (row ORDER: this row runs before `DivRow`). Runtime premises: the live `growslice`,
`memclrNoHeapPointers`, `gcWriteBarrier2`, `makeslice`, `memmove` contracts.
`Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, toy allocator, budget `0x80000`), a 48 KiB stack, the
threshold globals, `q.divRecursiveStep(u, v, 0, nil, stk)` with `q = [0]`, `u = [1, 0, 0]`, `v = [0, 2^63]`, the stack
`{w, len 0, cap 4}`; one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.DrsRow

open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

theorem mul_ns : NatMul.names.contains DivRec.fn = false := by decide

theorem mul_code (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn ((Extracted.program.onlySegments NatMul.names).link impl) (LibDrs.program.link impl) := by
  rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide))

/-- **`nat.divRecursiveStep`** (arm64): `z.divRecursiveStep(u, v, depth, tmp, stk)` (`len v ≥ 2`, `v`'s top bit set,
`z = 0`, `2U < B^(len v + len z)`) stores `U / V` in `z[0 : len z]` and `U mod V` in `u`, restores the stack's `len`;
writes only `z`, `u`, the stack, the runtime's memory and the window; for every runtime meeting the live contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc d : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivLarge.drsFn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc, d]
      (fun s => DivLarge.DrsPre R b L (DivRec.drsC (stLen s.mem st.toNat) ul.toNat vl.toNat) qp.toNat ql.toNat qc.toNat
        st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s)
      (fun s s' => DivLarge.DrsPost R b L (DivRec.drsC (stLen s.mem st.toNat) ul.toNat vl.toNat) qp.toNat ql.toNat
        st.toNat up.toNat ul.toNat vp.toNat vl.toNat s s') :=
  Ensures.full hap (DivRec.hyp impl hap R NatMul.names mul_ns (mul_code impl hap)
    (NatMul.hypXE impl hap R hmk hgr hmc hmv hwb) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmv
    b L qp ql qc st up ul uc vp vl vc d)

end FvModexp.Arm64.DrsRow

namespace FvModexp.Arm64.DrsRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x40` -/
abbrev VP : Nat := OB + 0x40

/-- `u = [1, 0, 0]` at `OB`, `v = [0, 2^63]` at `VP`, the stack header at `ST`, the threshold globals, all other
witness bytes 0 (`q = [0]` at `OA`) -/
def g (a : Nat) : Byte :=
  if a = OB then 1 else if a = VP + 15 then 0x80
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xA0 else if a = ST + 16 then 4
  else if a = gA then 40 else if a = gA + 8 then 40 else if a = gA + 16 then 12 else if a = gA + 24 then 80 else 0

/-- a 48 KiB stack, the other standard regions, `runtime.writeBarrier`'s flag word, the threshold globals -/
def regs : List Region := ⟨SP0 - 0xC000, 0xC100, true⟩ :: stdRegs.tail ++ [⟨StackNat.wbA, 8, false⟩, ⟨gA, 32, false⟩]

abbrev mem0 : Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 3, 3, BitVec.ofNat 64 VP, 2, 2, 0]

def s0 : State :=
  { regs := fun i => if h : i < args.length then args[i] else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 (segAddr Extracted.program DivLarge.drsFn),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x80000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

theorem rtOut (a n : Nat) (h : WBUF + 64 ≤ a ∧ a + n ≤ HEAP) : Outside a n R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; simp only [BUMP, HEAP, WBUF] at *; omega

theorem len0 : stLen mem0 ST = 0 := by decide +kernel

theorem cost0 : DivRec.drsC (stLen mem0 ST) 3 2 ≤ 0x80000 := by
  rw [len0, DivRec.drsC_small (by decide)]; decide +kernel

theorem pre : DivLarge.DrsPre R 0x80000 [] (DivRec.drsC (stLen s0.mem ST) 3 2) OA 1 1 ST OB 3 3 VP 2 2 s0 := by
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.sp = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 28 = BitVec.ofNat 64 G0 := rfl
  simp only [DivLarge.DrsPre, DivLarge.DrsPreW, CallEnv, Globals, EvenHyp.StkIn, ExpHyp.StackOK', StkOK, hm, hsp, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, cost0, inv1 _⟩
  all_goals try and_intros
  all_goals first
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | (intro r hr; simp at hr; done)
    | (intros; trivial)
    | (intro p c hpc hc; rcases hpc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> exact absurd hc (by omega))
    | (intro _; and_intros <;> first
        | (simp only [acc0] <;> decide +kernel)
        | exact Or.inr (rtOut _ _ (by decide +kernel))
        | (simp only [win, stW, stCap, outside_cons, outside_nil, and_true] <;> decide +kernel)
        | (unfold Apart <;> decide +kernel)
        | decide +kernel)
    | (simp only [NatLive]; intro h; exact absurd h (by decide))
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (show _ = _; decide)
    | (exact Or.inr (rtOut _ _ (by decide +kernel)))
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)),
        by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (intro h; exact absurd h (by decide))
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (intro _; exact ⟨by unfold Apart; decide +kernel, by unfold Apart; decide +kernel⟩)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | (simp only [natVal] <;> decide +kernel)
    | (simp only [Held, InRanges] <;> exact Or.inr (rtOut _ _ (by decide +kernel)))
    | decide +kernel

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program DivLarge.drsFn)
    args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, empty live set, `q = [0]`, `u = [1, 0, 0]`, `v = [0, 2^63]`, depth 0; one call-site state per
runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc vp vl vc d : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program DivLarge.drsFn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc, d] s ∧
    DivLarge.DrsPre R b L (DivRec.drsC (stLen s.mem st.toNat) ul.toNat vl.toNat) qp.toNat ql.toNat qc.toNat st.toNat
      up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
      DivLarge.DrsPost R b L (DivRec.drsC (stLen s.mem st.toNat) ul.toNat vl.toNat) qp.toNat ql.toNat st.toNat up.toNat
        ul.toNat vp.toNat vl.toNat s s' :=
  ⟨WStubs.impl, R, 0x80000, [], BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 3, 3,
    BitVec.ofNat 64 VP, 2, 2, 0, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _) (by rw [WStubs.addr_mv]; exact WStubs.mv R) 0x80000 []
      (BitVec.ofNat 64 OA) 1 1 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 3 3 (BitVec.ofNat 64 VP) 2 2 0 RET hret s0
      setup pre⟩

end FvModexp.Arm64.DrsRow.Witness
