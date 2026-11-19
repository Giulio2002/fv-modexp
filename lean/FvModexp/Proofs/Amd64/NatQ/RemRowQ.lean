import FvModexp.Proofs.Amd64.NatQ.RemC
import FvModexp.Proofs.Amd64.NatQ.DivCG
import FvModexp.Proofs.Amd64.NatQ.RemRowWitQ
import FvModexp.Proofs.Amd64.NatQ.DivRowWitQ
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.StubsGrow
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# Row (Q-form): `nat.rem` (amd64) on the Run extraction — `NHyp.RemHypQ … 41720 112 need (Q.NatDiv.costQ Q.drsCQ)`
moved to `Extracted.program.link impl` (`Ensures.full64`). Arguments: `z = (AX, BX, CX)`, `stk = DI`, `u = (SI, R8, R9)`,
`v` as three stack words, stated as explicit reads at `RSP + 8/16/24`.
`nat.div` discharged by top's `Q.NatDiv.ensCL` (all callees closed; only the live runtime contracts remain).
`Witness.nonvacuous`: RemRowWitQ's state (`u = 7`, `v = 3`, `z = nil`, stack `{w, 0, 4}`), one call-site state per contract;
a typing anchor `(v = VP ∧ vl = 1 ∧ vc = 1)` precedes the stack-argument reads (the audit re-elaborates the printed
statement, where `v.toNat` alone leaves `v`'s type unknown).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.RemRowQ

/-- the row's precondition (the three header reads of `Run`'s arguments, then `RemPreQ`) survives writing the return address: the header words are
read at `RSP + 8 .. RSP + 24` (apart from the slot `[RSP, RSP + 8)`), `RemPreQ` is `Q.NatRem.rempre_setRet` -/
theorem remrow_pre_setRet (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64)
    (p : Janus.Amd64.Program) (entry : Nat) (args : List W64) :
    Ensures.SetRetInv p entry args (fun s => s.mem.readLE ((s.regs 4).toNat + 8) 8 = v.toNat ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl.toNat ∧
        s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc.toNat ∧
        NHyp.RemPreQ R b H L 41720 112 z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat
          vc.toNat (Q.NatRem.need ul.toNat vl.toNat) (Q.NatDiv.costQ Q.drsCQ ul.toNat vl.toNat + stkR H s.mem st.toNat) s) := by
  intro s ret hs hret hp
  obtain ⟨h1, h2, h3, hq⟩ := hp
  have e8 : (s.setRet ret).mem.readLE (((s.setRet ret).regs 4).toNat + 8) 8 = s.mem.readLE ((s.regs 4).toNat + 8) 8 := by
    simp only [Janus.Amd64.GoABI.setRet_regs]; exact readLE_setRet_of_disjoint (by omega)
  have e16 : (s.setRet ret).mem.readLE (((s.setRet ret).regs 4).toNat + 16) 8 = s.mem.readLE ((s.regs 4).toNat + 16) 8 := by
    simp only [Janus.Amd64.GoABI.setRet_regs]; exact readLE_setRet_of_disjoint (by omega)
  have e24 : (s.setRet ret).mem.readLE (((s.setRet ret).regs 4).toNat + 24) 8 = s.mem.readLE ((s.regs 4).toNat + 24) 8 := by
    simp only [Janus.Amd64.GoABI.setRet_regs]; exact readLE_setRet_of_disjoint (by omega)
  exact ⟨by rw [e8]; exact h1, by rw [e16]; exact h2, by rw [e24]; exact h3,
    Q.NatRem.rempre_setRet R H b L z zl zc st u ul uc v.toNat vl.toNat vc.toNat Q.NatRem.need (Q.NatDiv.costQ Q.drsCQ) p entry args s ret hs hret hq⟩

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
    (H b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program Q.NatRem.fn) [z, zl, zc, st, u, ul, uc]
      (fun s => s.mem.readLE ((s.regs 4).toNat + 8) 8 = v.toNat ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl.toNat ∧
        s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc.toNat ∧
        NHyp.RemPreQ R b H L 41720 112 z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat
          vc.toNat (Q.NatRem.need ul.toNat vl.toNat) (Q.NatDiv.costQ Q.drsCQ ul.toNat vl.toNat + stkR H s.mem st.toNat) s)
      (fun s s' => NHyp.CPostRQ R b L 41720 112 z.toNat zc.toNat st.toNat
        (natVal s.mem u.toNat ul.toNat % natVal s.mem v.toNat vl.toNat)
        (Q.NatDiv.costQ Q.drsCQ ul.toNat vl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) s s') := by
  refine Ensures.of_old (remrow_pre_setRet R H b L z zl zc st u ul uc v vl vc _ _ _) ?_
  exact (fun ret hret s hs ⟨_, _, _, hpre⟩ =>
    (Ensures.full64 (hinv := Q.NatRem.rempre_setRet R H b L z zl zc st u ul uc v.toNat vl.toNat vc.toNat Q.NatRem.need (Q.NatDiv.costQ Q.drsCQ) _ _ _) hap (by simp [numIntRegs])
      (Q.NatRem.ens impl hap R hgr hmc hwb (Q.NatDiv.ensCL impl hap R hgr hmc hwb hmk hmv hmz)
        H b L z zl zc st u ul uc v.toNat vl.toNat vc.toNat)).toOld ret hret s hs hpre)

end FvModexp.Amd64.RemRowQ

namespace FvModexp.Amd64.RemRowQ.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy
open FvModexp.Amd64.DivRowQ.Witness (mvzSite site_mvz)

set_option maxRecDepth 100000

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x80000`, reserve level `96`, empty live set, `z.rem(stk, u, v)` with `z = nil`, `u = 7`, `v = 3`; one
call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
    (z zl zc st u ul uc v vl vc : BitVec 64) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program Q.NatRem.fn)
      [z, zl, zc, st, u, ul, uc] s ∧
    -- typing anchor for the stack-argument words: the witness's v = 3 at `VP`, one limb
    (v = BitVec.ofNat 64 VP ∧ vl = 1#64 ∧ vc = 1#64) ∧
    (s.mem.readLE ((s.regs 4).toNat + 8) 8 = v.toNat ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl.toNat ∧
      s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc.toNat ∧
      NHyp.RemPreQ R b H L 41720 112 z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat
        vc.toNat (Q.NatRem.need ul.toNat vl.toNat) (Q.NatDiv.costQ Q.drsCQ ul.toNat vl.toNat + stkR H s.mem st.toNat) s) ∧
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
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧
      NHyp.CPostRQ R b L 41720 112 z.toNat zc.toNat st.toNat
        (natVal (s.setRet ret).mem u.toNat ul.toNat % natVal (s.setRet ret).mem v.toNat vl.toNat)
        (Q.NatDiv.costQ Q.drsCQ ul.toNat vl.toNat + stkR H (s.setRet ret).mem st.toNat) (stkR H s'.mem st.toNat) (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 96, 0x80000, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 OB, 1, 1, BitVec.ofNat 64 VP, 1, 1,
    RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    hret, setup, ⟨rfl, rfl, rfl⟩, ⟨words.1, words.2.1, words.2.2, pre (Q.NatDiv.costQ Q.drsCQ) cost0Q⟩,
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
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R) 96 0x80000 []
      0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 OB) 1 1 (BitVec.ofNat 64 VP) 1 1 s0 setup
      ⟨words.1, words.2.1, words.2.2, pre (Q.NatDiv.costQ Q.drsCQ) cost0Q⟩ RET hret⟩

end FvModexp.Amd64.RemRowQ.Witness
