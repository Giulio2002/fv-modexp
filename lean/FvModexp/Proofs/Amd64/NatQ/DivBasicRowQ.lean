import FvModexp.Proofs.Amd64.NatQ.DivBasic
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row: `nat.divBasic` (amd64) on the Run extraction — the twin of Arm64/Nat/DivBasicRow.lean

`correctness` = `Q.DivBasic.ensL` (Q-form, TIGHT COSTS, top s38; reserve level `H`) (its `(*stack).nat` call discharged inside by `StackNatX.hypQ`), moved to
`Extracted.program.link impl` (`Ensures.full64`); runtime premises: the live `growslice`, `memclrNoHeapPointers` and
`gcWriteBarrier2` contracts. The register arguments are `q, stk, u`; `v` is passed on the stack (`Pre`: `v`'s pointer
and length at `RSP + 8` / `RSP + 16`). `Witness.nonvacuous`: the shared witness runtime, the toy allocator invariant,
the Run extraction's read-only data, the `runtime.writeBarrier` flag word, and the call `divBasic(q, stk, u, v)` with
`u = [5, 2^63 + 1]`, `v = [0, 2^63]` (`U / V = 1`), `len q = 1`, a stack `{w, len 0, cap 4}`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasicRowQ

/-- **`nat.divBasic`** (amd64): `q = divBasic(stk, u, v)` stores `U / V` in `q[0 : qn]` and `U mod V` in `u`, returns
the stack with its `len` (`StackBackL`); writes only `q[0 : qn]`, `u`, the stack header and free part, the runtime's
memory and the window. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivBasic.fn) [qp, ql, qc, st, up, ul, uc]
      (Q.DivBasic.Pre R b H L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl)
      (Q.DivBasic.PostL R b H L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl) :=
  Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Amd64.Q.DivBasic.Pre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.win, FvModexp.natVal, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.DivBasic.freeP, FvModexp.Amd64.DivBasic.freeN, FvModexp.stLen, FvModexp.stkR, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.stkRes, FvModexp.potK]) hap (by simp [numIntRegs]) (Q.DivBasic.ensL impl hap R hgr hmc hwb H b L qp ql qc st up ul uc vp vl)

end FvModexp.Amd64.DivBasicRowQ

namespace FvModexp.Amd64.DivBasicRowQ.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- the stack header at `ST = OA + 0x100`: `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `v` at `VP = OB + 0x100` -/
abbrev VP : Nat := OB + 0x100

/-- `u = [5, 2^63 + 1]` at `OB`, `v = [0, 2^63]` at `VP`, the stack header at `ST`, `v`'s slice header (stack
argument) at `SP0 + 8`, all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OB then 5 else if a = OB + 8 then 1 else if a = OB + 15 then 0x80 else if a = VP + 15 then 0x80
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = SP0 + 9 then 0x01 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 2
  else if a = SP0 + 24 then 2 else 0

/-- the standard regions plus the `runtime.writeBarrier` flag word -/
def regs : List Janus.Arm64.Region := stdRegs ++ [⟨StackNat.wbA, 8, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 2, 2]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 1 else if i = 1 then 1
      else if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 OB else if i = 8 then 2
      else if i = 9 then 2 else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program DivBasic.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program DivBasic.fn)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) :
    mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

/-- the toy runtime's invariant for the witness memory (as `AsmWit.inv0`, with the extra region) -/
theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  show wbytes (toyBytes g) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem pre : Q.DivBasic.Pre R 0x1000 6 [] OA 1 ST OB 2 2 VP 2 s0 := by
  have hm : s0.mem = mem0 := rfl
  refine ⟨⟨?_, ?_, by decide, dataLoaded _ _, ?_, ?_, ?_, fun r hr => by simp at hr, roOut, ⟨?_, ?_, ?_⟩⟩,
    WStubs.serves [], ?_⟩
  all_goals try and_intros
  all_goals first
    | exact inv1 _
    | (intro r hr; simp at hr; done)
    | (intro _; and_intros <;> first
        | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
        | (simp only [Apart]; decide +kernel)
        | decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_nil]; done)
    | (simp only [List.nil_append, List.map_nil, outside_nil]; done)
    | (simp only [List.append, List.map, outside_nil]; done)
    | (simp only [List.append, List.map, outside_cons, outside_nil, and_true]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel⟩; rw [hm, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩; rw [hm, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_⟩; rw [hm, acc0]; decide +kernel)
    | (refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩; rw [hm, acc0]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [DivBasic.freeP, DivBasic.freeN, stW, stLen, stCap, Apart, win, outside_cons, outside_nil,
        and_true, hm]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [hm, acc0]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, stW, stLen, stCap, InRanges, outside_cons, outside_nil, and_true, rt_eq,
        hm, acc0]; decide +kernel)
    | (simp only [Held, InRanges, outside_cons, outside_nil, and_true, rt_eq]; decide +kernel)
    | (simp only [stkR, stkRes, stLen, stCap, hm]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, `divBasic(q, stk, u, v)` with `u = [5, 2^63 + 1]`, `v = [0, 2^63]`, `len q = 1`; one
call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program DivBasic.fn)
      [qp, ql, qc, st, up, ul, uc] s ∧
    Q.DivBasic.Pre R b H L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ Q.DivBasic.PostL R b H L qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 6, 0x1000, [], BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 2, 2, VP, 2, RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 6 0x1000 []
      (BitVec.ofNat 64 OA) 1 1 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 2 2 VP 2 s0 setup pre RET hret⟩

end FvModexp.Amd64.DivBasicRowQ.Witness
