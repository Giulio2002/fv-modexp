import FvModexp.Proofs.Arm64.Int.IntASRow

/-!
# Row: `(*Int).Sub` (arm64) on the Run extraction

Same proof as `IntASRow` (`IntAS.ens … true`); witness `z.Sub(5, 9)` on `IntASRow.Witness`'s memory.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.IntSubRow

/-- **`(*Int).Sub`** (arm64): as `IntASRow.correctness`, with `x - y`. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub") [z, x, y]
      (IntAS.Pre R b L z.toNat x.toNat y.toNat) (IntAS.Post true R b L z.toNat x.toNat y.toNat) :=
  Ensures.full (hinv := by janus_pre_setRet [FvModexp.Arm64.IntAS.Pre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.NatAdd.wordT, FvModexp.Arm64.IntAS.OpR, FvModexp.Arm64.win, FvModexp.Arm64.IntAS.wbA, FvModexp.Arm64.IntAS.hC, FvModexp.NatLive, FvModexp.Arm64.IntAS.hP, FvModexp.Arm64.IntAS.hL, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.IntAS.hNeg, FvModexp.NatNorm]) hap (IntAS.ens impl hap R hmk hmv hwb true b L z x y)

end FvModexp.Arm64.IntSubRow

namespace FvModexp.Arm64.IntSubRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy FvModexp.Arm64.IntASRow.Witness

set_option maxRecDepth 100000

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime
(toy `makeslice`, looping `memmove`, toy write barrier), budget `0x1000`, empty live set, the call `z.Sub(x, y)` with
`x = 5`, `y = 9`, `z`'s array of capacity 2; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z x y : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub") [z, x, y] s ∧
    IntAS.Pre R b L z.toNat x.toNat y.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ IntAS.Post true R b L z.toNat x.toNat y.toNat (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), BitVec.ofNat 64 (OA + 0x80),
    RET, s0 true, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setupSub, pre true,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 0x1000 []
      (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) (BitVec.ofNat 64 (OA + 0x80)) (s0 true) setupSub (pre true) RET hret⟩

end FvModexp.Arm64.IntSubRow.Witness
