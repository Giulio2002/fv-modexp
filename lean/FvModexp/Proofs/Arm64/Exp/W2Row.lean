import FvModexp.Proofs.Arm64.Exp.W2FunE
import FvModexp.Proofs.Arm64.Exp.W2Wit
import FvModexp.Proofs.Arm64.Exp.DivInst
import FvModexp.Proofs.Arm64.Nat.RowLink
import FvModexp.Proofs.Arm64.Witness.Sites
import FvModexp.Proofs.Arm64.Witness.StubsMvz
import FvModexp.Proofs.Arm64.Int.ModRowW

set_option autoImplicit false

/-!
# Row: `nat.expNNOddMontgomeryWindowSize2` (arm64) on the Run extraction

`correctness` = `ExpW2.ens` with asm's CLOSED `nat.div` (`DivInst.hyp` = `NatDiv.ensCL`: program `LibDiv.names`, stack
`41504`, cost `DivInst.divC`) moved to `Extracted.program.link impl` (`Ensures.full`). Runtime premises: the live
`memclrNoHeapPointers`, `memmove`, `makeslice`, `growslice`, `gcWriteBarrier2` contracts and the zero-length `memmove`
contract (Janus PR #2 `MemmoveZeroLive`, local copy until the v0.3.1 re-pin: this row passes the audit only then).
`Witness.nonvacuous`: the window-2 witness state (`ExpW2.Witness.s0`: `z = nil`, `3^5 mod 7`, a 64 KiB stack region,
window depth `K = 41504`), the shared witness runtime, one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Row

/-- **window-2** (arm64): `z.expNNOddMontgomeryWindowSize2(stk, x, y, m)` returns `x^y mod m` (`ExpW2.Pre`/`Post`:
odd `m`, `len x ≤ len m`, the Montgomery window loop over every word of `y`) for every runtime meeting the live
allocation / copy / clear / write-barrier contracts; window depth `K ≥ 41504` (`nat.div`'s). -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hK : 41504 ≤ K)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ExpW2.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 ylen, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc]
      (ExpW2.Pre R b L K DivInst.divC zp zc st xp xl xc yp ylen mp n mc)
      (ExpW2.Post R b L K DivInst.divC zp zc st xp xl yp ylen mp n) :=
  Ensures.full hap (ExpW2.ens impl hap R hclr hmv hmk hgr hwb LibDiv.names 41504 DivInst.divC
    (DivInst.hyp impl hap R hgr hclr hwb hmk hmv hmz) DivInst.ns_sub DivInst.ns_w2 b L K hK (by omega)
    zp zl zc st xp xl xc yp ylen yc mp n mc)

end FvModexp.Arm64.W2Row

namespace FvModexp.Arm64.W2Row.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy FvModexp.Arm64.ExpW2.Witness

set_option maxRecDepth 100000

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program ExpW2.fn)
    args s0 :=
  ⟨rfl, rfl, fun i h => by simp only [s0, dif_pos h]⟩

/-- the closed `nat.div`'s cost at the witness call (`len m = len x = 1`, empty stack) fits the witness bound -/
theorem divc : ExpW2.divCost DivInst.divC 1 1 0 ≤ CD := by
  simp only [ExpW2.divCost, DivInst.divC, NatDiv.cost, DivLarge.cost]
  simp (disch := omega) only [DivRec.drsC_small]
  decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, window depth `41504`, the call `z.expNNOddMontgomeryWindowSize2(stk, 3, 5, 7)` with
`z = nil` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    41504 ≤ K ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program ExpW2.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 ylen, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc] s ∧
    ExpW2.Pre R b L K DivInst.divC zp zc st xp xl xc yp ylen mp n mc s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      (s_c.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s_c ∧
      LiveMemAt R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 1).toNat,
        (s_c.regs 2).toNat] L b s_c (calleeStack s_c 4096 3)) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ ExpW2.Post R b L K DivInst.divC zp zc st xp xl yp ylen mp n s s' :=
  ⟨WStubs.impl, R, BW, [], 41504, 0, 0, 0, ST, XP, 1, 1, YP, 1, 1, MP, 1, 1, RET, s0, WStubs.hap,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, Nat.le_refl _, hret, setup,
    pre 41504 DivInst.divC (by decide) (by decide) divc,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact AsmWit.site_mz _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) BW [] 41504 (Nat.le_refl _)
      0 0 0 ST XP 1 1 YP 1 1 MP 1 1 RET hret s0 setup (pre 41504 DivInst.divC (by decide) (by decide) divc)⟩

end FvModexp.Arm64.W2Row.Witness
