import FvModexp.Proofs.Arm64.NatQ.DrsStep
import FvModexp.Proofs.Arm64.NatQ.DrsRowWQ
import FvModexp.Proofs.Arm64.NatQ.MulE
import FvModexp.Proofs.Arm64.Nat.RowLink

set_option autoImplicit false

/-!
# Row: `nat.divRecursiveStep` (arm64) on the Run extraction, Q-form (TIGHT COSTS) — `Q.DivLarge.DrsHypQ` at `Q.drsCQ`

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

namespace FvModexp.Arm64.DrsRowQ
open FvModexp.Arm64.DrsRow

open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

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
    (H b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc d : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivLarge.drsFn)
      [qp, ql, qc, st, up, ul, uc, vp, vl, vc, d]
      (fun s => Q.DivLarge.DrsPre R b L H (Q.drsCQ ul.toNat vl.toNat) qp.toNat ql.toNat qc.toNat
        st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s)
      (fun s s' => Q.DivLarge.DrsPost R b L H (Q.drsCQ ul.toNat vl.toNat) qp.toNat ql.toNat
        st.toNat up.toNat ul.toNat vp.toNat vl.toNat s s') :=
  Ensures.full hap (Q.DivRec.hyp impl hap R NatMul.names mul_ns (mul_code impl hap)
    (Q.NatDiv.mulE (Q.NatMul.hypQE impl hap R hmk hgr hmc hmv hwb)) (Nat.le_refl _) (Nat.le_refl _) hgr hmc hwb hmv
    H b L qp ql qc st up ul uc vp vl vc d)

end FvModexp.Arm64.DrsRowQ

namespace FvModexp.Arm64.DrsRowQ.Witness
open FvModexp.Arm64.DrsRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, empty live set, `q = [0]`, `u = [1, 0, 0]`, `v = [0, 2^63]`, depth 0; one call-site state per
runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
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
    Q.DivLarge.DrsPre R b L H (Q.drsCQ ul.toNat vl.toNat) qp.toNat ql.toNat qc.toNat st.toNat
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
      Q.DivLarge.DrsPost R b L H (Q.drsCQ ul.toNat vl.toNat) qp.toNat ql.toNat st.toNat up.toNat
        ul.toNat vp.toNat vl.toNat s s' :=
  ⟨WStubs.impl, R, 88, 0x80000, [], BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 3, 3,
    BitVec.ofNat 64 VP, 2, 2, 0, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    hret, setup, preQ,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _) (by rw [WStubs.addr_mv]; exact WStubs.mv R) 88 0x80000 []
      (BitVec.ofNat 64 OA) 1 1 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 3 3 (BitVec.ofNat 64 VP) 2 2 0 RET hret s0
      setup preQ⟩

end FvModexp.Arm64.DrsRowQ.Witness
