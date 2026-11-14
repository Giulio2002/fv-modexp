import FvModexp.Proofs.Amd64.Exp.W4Wit
import FvModexp.Proofs.Amd64.Exp.W4RowPre
import FvModexp.Proofs.Amd64.Exp.DivInst
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsMvz
import FvModexp.Proofs.Amd64.Witness.StubsGrow
import FvModexp.Proofs.Amd64.NatQ.DivRowWitQ

set_option autoImplicit false

/-!
# Row: `nat.expNNOddMontgomeryWindowSize4` (amd64) on the Run extraction (agent expmc s67; twin of Arm64/Exp/W4Row)

`correctness` = `ExpW4.ens` with top's CLOSED `nat.div` (`DivInst.hyp` = `Q.NatDiv.ensCL` bridged by
`DivInst.divL_of_Q`: program `Q.NatDiv.names`, stack `41512`, cost `DivInst.divC`) moved to `Extracted.program.link impl`
(`Ensures.full64`). Runtime premises: the live `memclrNoHeapPointers`, `memmove`, `makeslice`, `growslice`,
`gcWriteBarrier2` contracts and the zero-length `memmove` contract (`MemmoveZeroLive64`). `y`, `m` (with `len m`,
`cap m`) are the stack arguments at `RSP + 8 …` (`ExpW4.PreR`: `PreD` with the stack-argument reads written
as `readLE ((RSP).toNat + k)`, the form Janus's `[RSP]`-word audit accepts;
`preD_of_preR`). `costD` bounds `nat.div`'s cost at the levels the window calls it on (`PreD`'s `XnB`); `PostD` charges it.
`Witness.nonvacuous`: the window-4 witness state (`ExpW4.Witness.s0`: `z = nil`, `3^5 mod 7`, a 64 KiB stack region,
window depth `K = 41512`), `costD = CD`, the shared witness runtime, one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Row

/-- **window-4** (amd64): `z.expNNOddMontgomeryWindowSize4(stk, x, y, m)` returns `x^y mod m` (`ExpW4.PreR`/`PostD`:
odd `m`, `len x ≤ len m`, the Montgomery window loop over every word of `y`) for every runtime meeting the live
allocation / copy / clear / write-barrier contracts; window depth `K ≥ 41512` (`nat.div`'s). -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hK : 41512 ≤ K)
    (costD zp zl zc st xp xl xc yp ylen mp n mc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program W4Loop.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc]
      (ExpW4.PreR R b L K DivInst.divC costD zp zc st xp xl xc yp ylen mp n mc)
      (ExpW4.PostD R b L K costD zp zc st xp xl yp ylen mp n) :=
  Ensures.mono (Ensures.full64 hap (by simp [numIntRegs])
    (ExpW4.ens impl hap R hclr hmv hmk hgr hwb Q.NatDiv.names 41512 DivInst.divC
      (DivInst.hyp impl hap R hgr hclr hwb hmk hmv hmz) DivInst.ns_sub DivInst.ns_w4 b L K hK
      costD zp zl zc st xp xl xc yp ylen mp n mc))
    (fun _ h => ExpW4.preD_of_preR h) (fun _ _ _ h => h)

end FvModexp.Amd64.W4Row

namespace FvModexp.Amd64.W4Row.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy FvModexp.Amd64.ExpW4.Witness

set_option maxRecDepth 100000

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- the closed `nat.div`'s bridged cost on window-4's two division shapes at every level `≤ 0x200` fits `CD`
(`stkRes H = 160·H + 440`; `costQ drsCQ 3 1 = 464`, `costQ drsCQ 1 1 = 240`) -/
theorem divc : ∀ l, l ≤ 0x200 → DivInst.divC l 3 1 ≤ CD ∧ DivInst.divC l 1 1 ≤ CD := by
  intro l hl
  have h3 : Q.NatDiv.costQ Q.drsCQ 3 1 ≤ 464 := by decide +kernel
  have h1 : Q.NatDiv.costQ Q.drsCQ 1 1 ≤ 240 := by decide +kernel
  simp only [DivInst.divC, DivInst.divBr, stkRes_eq, CD]
  omega

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, window depth `41512`, `costD = CD`, the call `z.expNNOddMontgomeryWindowSize4(stk, 3, 5, 7)`
with `z = nil` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat)
    (costD zp zl zc st xp xl xc yp ylen mp n mc : Nat) (ret : Nat) (s : State),
    (yp = YP ∧ ylen = 1 ∧ mp = MP ∧ n = 1 ∧ mc = 1) ∧
    Amd64.ImplApart Extracted.program impl ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    41512 ≤ K ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program W4Loop.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc] s ∧
    ExpW4.PreR R b L K DivInst.divC costD zp zc st xp xl xc yp ylen mp n mc s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      DivRowQ.Witness.mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ ExpW4.PostD R b L K costD zp zc st xp xl yp ylen mp n s s' :=
  ⟨WStubs.impl, R, BW, [], KW, CD, 0, 0, 0, ST, XP, 1, 1, YP, 1, MP, 1, 1, RET, s0,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, WStubs.hap,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, Nat.le_refl _, hret, setup,
    ExpW4.preR_of_preD (pre DivInst.divC divc),
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact DivRowQ.Witness.site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) BW [] KW (Nat.le_refl _)
      CD 0 0 0 ST XP 1 1 YP 1 MP 1 1 RET hret s0 setup (ExpW4.preR_of_preD (pre DivInst.divC divc))⟩

end FvModexp.Amd64.W4Row.Witness
