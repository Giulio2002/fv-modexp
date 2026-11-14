import FvModexp.Proofs.Amd64.NatQ.DrsRowWQ
import FvModexp.Proofs.Amd64.NatQ.DrsRowWitQ
-- row ORDER (as arm64 DrsRowQ, asm s43): not used by this row; imported so that the divLarge/nat.div program modules
-- are compiled (and replayed) here, by the earlier row, instead of on DivRowQ's critical path.
import FvModexp.Proofs.Amd64.Nat.LibDiv
import FvModexp.Proofs.Amd64.Nat.LibDivL
set_option autoImplicit false

/-!
# Row: `nat.divRecursiveStep` (amd64) on the Run extraction, Q-form (TIGHT COSTS) — the twin of Arm64/NatQ/DrsRowQ.lean

`correctness` = `Q.DivRec.hyp` (asm s54) with divmc's Q `nat.mul` (`Q.NatMul.hypQE`) for its `nat.mul` calls, moved to
`Extracted.program.link impl` (`Ensures.full64`); window `40960` below / `96` above `RSP`. Statement:
`Q.DivLarge.DrsPre` → `Q.DivLarge.DrsPost` (`q[0 : len q] = U / V`, `u = U mod V`, the stack restored, `StackBackL`).
The register arguments are `q, stk, u, depth`; `v = (vp, vl, vc)` is passed on the stack (`DrsPre`: the words at
`RSP + 8 / + 16 / + 24`). Runtime premises: the live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`, `makeslice`,
`memmove` contracts.
`Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`, toy allocator, budget `0x80000`), a 48 KiB stack, the
threshold globals (`divRecursiveThreshold = 40`), `q.divRecursiveStep(u, v, 0, nil, stk)` with `q = [0]`,
`u = [1, 0, 0]`, `v = [0, 2^63]`, the stack `{w, len 0, cap 4}`; one call-site state per contract.
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel FvModexp
namespace FvModexp.Amd64.DrsRowQ

/-- **`nat.divRecursiveStep`** (amd64): `q[0 : len q] = U / V`, `u = U mod V` (`DrsPost`), the stack restored with its
`len` (`StackBackL`); writes only `q`, `u`, the stack header and free part, the runtime's memory and the window. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (H b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc d : BitVec 64) (vp vl vc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program DivLarge.drsFn)
      [qp, ql, qc, st, up, ul, uc, d]
      (fun s => Q.DivLarge.DrsPre R b L H (Q.drsCQ ul.toNat vl) qp.toNat ql.toNat qc.toNat
        st.toNat up.toNat ul.toNat uc.toNat vp vl vc s)
      (fun s s' => Q.DivLarge.DrsPost R b L H (Q.drsCQ ul.toNat vl) qp.toNat ql.toNat
        st.toNat up.toNat ul.toNat vp vl s s') :=
  Ensures.full64 hap (by simp [numIntRegs]) (Q.DivRec.hyp impl hap R Q.NatMul.names mul_ns (mul_code impl hap)
    (Q.NatMul.hypQE impl hap R hmk hgr hmc hmv hwb _) hgr hmc hwb hmv H b L qp ql qc st up ul uc d vp vl vc)
end FvModexp.Amd64.DrsRowQ

namespace FvModexp.Amd64.DrsRowQ.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, empty live set, `q = [0]`, `u = [1, 0, 0]`, `v = [0, 2^63]`, depth 0; one call-site state per
runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc d : BitVec 64) (vp vl vc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program DivLarge.drsFn)
      [qp, ql, qc, st, up, ul, uc, d] s ∧
    -- typing anchor for the stack-argument words (the audit re-elaborates the printed statement, whose ∃ binders carry
    -- no types; divmc s60): the witness's `v = [0, 2^63]` at `OB + 0x40`, two limbs
    (vp = 14680128 ∧ vl = 2 ∧ vc = 2) ∧
    Q.DivLarge.DrsPre R b L H (Q.drsCQ ul.toNat vl) qp.toNat ql.toNat qc.toNat st.toNat up.toNat ul.toNat uc.toNat
      vp vl vc s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
      Q.DivLarge.DrsPost R b L H (Q.drsCQ ul.toNat vl) qp.toNat ql.toNat st.toNat up.toNat ul.toNat vp vl s s' :=
  ⟨WStubs.impl, R, 88, 0x80000, [], BitVec.ofNat 64 OA, 1, 1, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 3, 3, 0,
    VP, 2, 2, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    hret, setup, ⟨rfl, rfl, rfl⟩, preQ,
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
      (BitVec.ofNat 64 OA) 1 1 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 3 3 0 VP 2 2 RET hret s0 setup preQ⟩

end FvModexp.Amd64.DrsRowQ.Witness
