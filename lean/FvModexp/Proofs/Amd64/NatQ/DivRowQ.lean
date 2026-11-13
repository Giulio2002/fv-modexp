import FvModexp.Proofs.Amd64.NatQ.DivCG
import FvModexp.Proofs.Amd64.NatQ.DivRowWitQ
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row (Q-form, TIGHT COSTS, top s46): `nat.div` (amd64, `stk ≠ nil`) on the Run extraction — `ExpSlow.DivHypLGQ` (`Q.NatDiv.ensCLG`, cost `Q.NatDiv.costQ Q.drsCQ` + `stkR H`) — twin of Arm64/NatQ/DivRowQ.lean

`correctness` = `Q.NatDiv.ensCLG` (every callee proved: `divW`, `cmp`, `divLarge` → `divBasic` / `divRecursiveStep` (asm) →
`nat.mul` (divmc), `(*stack).nat`) moved to `Extracted.program.link impl` (`Ensures.full64`); window `41512` below /
`112` above `RSP`; `u`, `v` passed on the stack (`RSP + 8 … + 48`, bound by the pre). Statement: `ExpSlow.DivPreGQ` →
`ExpSlow.DivPostLGQ` (`q = U / V`, `r = U mod V`, normalised, old-or-fresh arrays, results apart, `StackBackL`).
Runtime premises: the live `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`, `makeslice`, `memmove`
(+ `MemmoveZeroLive64`) contracts.
`Witness.nonvacuous`: the shared witness runtime (`WStubs.impl`), the state of `DivRowWitQ` (`z = z2 = nil`, `u = 7`,
`v = 3`, the stack `{w, len 0, cap 4}`, budget `0x80000`); one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.DivRowQ

/-- **`nat.div`** (amd64): `q, r = z.div(stk, z2, u, v)` (`v ≠ 0` normalised, `u` normalised and possibly empty,
`len ≤ 2^9`) returns `q = U / V`, `r = U mod V` (normalised, in `z` / `z2`'s array or fresh, apart from each other),
the stack restored; writes only `z`, `z2`, the stack, the runtime's memory and the window; for every runtime meeting
the live contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program Q.NatDiv.fn)
      [z, zl, zc, st, z2, z2l, z2c]
      (fun s => ExpSlow.DivPreGQ R b H (Q.NatDiv.costQ Q.drsCQ ul vl + stkR H s.mem st.toNat) L 41512 112 z.toNat
        zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
      (fun s s' => ExpSlow.DivPostLGQ R b (Q.NatDiv.costQ Q.drsCQ ul vl + stkR H s.mem st.toNat)
        (stkR H s'.mem st.toNat) L 41512 112 z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s') :=
  Ensures.full64 hap (by simp [numIntRegs])
    (Q.NatDiv.ensCLG impl hap R hgr hmc hwb hmk hmv hmz H b L z zl zc st z2 z2l z2c u ul uc v vl vc)

end FvModexp.Amd64.DivRowQ

namespace FvModexp.Amd64.DivRowQ.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, empty live set, `z.div(stk, z2, u, v)` with `z = z2 = nil`, `u = 7`, `v = 3`; one call-site state
per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
    (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program Q.NatDiv.fn)
      [z, zl, zc, st, z2, z2l, z2c] s ∧
    ExpSlow.DivPreGQ R b H (Q.NatDiv.costQ Q.drsCQ ul vl + stkR H s.mem st.toNat) L 41512 112 z.toNat zl.toNat
      zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s ∧
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
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
      ExpSlow.DivPostLGQ R b (Q.NatDiv.costQ Q.drsCQ ul vl + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L 41512
        112 z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s' :=
  ⟨WStubs.impl, R, 80, 0x80000, [], 0, 0, 0, BitVec.ofNat 64 ST, 0, 0, 0, OB, 1, 1, VP, 1, 1, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    hret, setup, pre Q.drsCQ cost0Q,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mvz _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R) 80 0x80000 []
      0 0 0 (BitVec.ofNat 64 ST) 0 0 0 OB 1 1 VP 1 1 RET hret s0 setup (pre Q.drsCQ cost0Q)⟩

end FvModexp.Amd64.DivRowQ.Witness
