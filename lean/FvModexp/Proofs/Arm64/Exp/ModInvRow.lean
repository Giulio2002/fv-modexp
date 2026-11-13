import FvModexp.Proofs.Arm64.Exp.ExpWit
import FvModexp.Proofs.Arm64.Exp.ModInv
import FvModexp.Proofs.Arm64.Exp.CalleeInstQ
import FvModexp.Proofs.Arm64.Nat.NatSub0
import FvModexp.Proofs.Arm64.Nat.NatAdd

set_option autoImplicit false

/-!
# Row: `nat.modularInverseModPowerOfTwo` (arm64) on the Run extraction (agent infra)

`correctness` = the Q-form `ModInv.ensQ` (TIGHT COSTS s45: per-round sizes, one reserve level `H`) with the PROVED
callees of `CalleeInstQ` (divmc's Q-form `nat.sqr` / `nat.mul`, asm's `nat.trunc`, `nat.lsh`),
`nat.sub` (divmc `NatSub.ensR0`), `nat.add` (divmc `NatAdd.ensR`), and `nat.subMod2N` (inside `ModInv.ens`), callee
frame bound `kc = sqrWX`, moved to `Extracted.program.link impl` (`Ensures.full`). Runtime premises: the live
`growslice`, `memclrNoHeapPointers`, `memmove`, `makeslice`, `gcWriteBarrier2` contracts.
`Witness.nonvacuous`: the shared witness memory `ExpWit` (`x = [3]`, the stack `{w, 0, 4}`, `natOne`), `z` = an
all-zero 2-word array, `n = 64`, reserve level `H = D 64 = 80`; one call-site state per contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInvRow

open FvModexp.Arm64.CalleeInstQ

set_option maxHeartbeats 64000000 in
theorem nfM : nsQ.contains ModInv.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nfS : nsQ.contains SubMod2N.fn = false := by decide

/-- **`nat.modularInverseModPowerOfTwo`** (arm64): `z.modularInverseModPowerOfTwo(stk, x, n)` returns the inverse of
odd `x` modulo `2^n` (`Exp.modularInverseModPowerOfTwo`, Q-form `ModInv.PreQ` / `PostQ`: cost
`ModInv.cost sqrCQ mulCQ xl n + stkR H s.mem st`), for every runtime meeting the live
allocation / copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (H B : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ModInv.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (ModInv.PreQ R NatSqr.sqrWX H sqrCQ mulCQ B L zp zl zc st xp xl xc n)
      (ModInv.PostQ R NatSqr.sqrWX H sqrCQ mulCQ B L zp zc st xp xl n) := by
  have hW := CalleeInst.sqrWX_eq
  have hsub : SubMod2N.SubHypR0 impl R := fun b L zp zl zc xp xl xc yp yl yc =>
    NatSub.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc
  have hadd : SubMod2N.AddHypR impl R := fun b L zp zl zc xp xl xc yp yl yc =>
    NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc
  exact Ensures.full hap (ModInv.ensQ hap sub nfM nfS hmk (by omega) (sq hap hgr hmc hmv hmk hwb) (Nat.le_refl _)
    (by omega) (tr hap hmv hmk) (by omega) (by omega) (mu hap hgr hmc hmv hmk hwb)
    (by rw [CalleeInst.mulWX_eq]; omega)
    (by omega) (lh hap hmc hmv hmk) (by omega) (by omega) (by omega) hsub hadd hgr sqm mum
    H B L zp zl zc st xp xl xc n)

end FvModexp.Arm64.ModInvRow

namespace FvModexp.Arm64.ModInvRow.Witness

open Janus.Contracts.Toy FvModexp.Arm64.AsmWit FvModexp.Arm64.ExpWit FvModexp.Arm64.ModInv FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp

set_option maxRecDepth 100000

/-- `z`'s (all-zero, 2-word) array -/
abbrev ZP : Nat := OA + 0x400

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 ZP, 0, 2, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, 64]

abbrev s0 : State := mkS (segAddr Extracted.program ModInv.fn) args

theorem g0 : (s0.regs 28).toNat = G0 := by decide

theorem bud : ModInv.cost sqrCQ mulCQ 1 64 + (stkRes 80 - potK * 4) ≤ BW := by decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies `PreQ` (`x = 3`, `n = 64`, `z` a 2-word array) at `H = 80` (`= 0 + D 64`) -/
theorem pre : ModInv.PreQ R NatSqr.sqrWX 80 sqrCQ mulCQ BW [] ZP 0 2 ST XP 1 1 64 s0 := by
  have hm : s0.mem = mem0 := rfl
  have hW := CalleeInst.sqrWX_eq
  unfold ModInv.PreQ
  rw [hm, stLen0, hW]
  simp only [CallEnv, winA, win, WrOut, RdIn, StkIn, StkApart, OneIn, PX, OpX, CapIn, frP, frN, StackOK', stWs, stkWs,
    g0, mkS_sp, stW0, stLen0, stCap0, K, A, stkR]
  repeat' apply And.intro
  all_goals first
    | decide
    | exact accWin _ _ (by decide) (by decide)
    | exact dataLoaded _ _
    | exact WStubs.serves []
    | exact roOut
    | exact inv1 _
    | exact bud
    | exact ⟨OP, one0 [] _ (by simp only [outside_cons, outside_nil, and_true]; decide)
        (by simp only [outside_cons, outside_nil, and_true]; decide), by simp only [Apart, nA_eq]; decide,
        by simp only [Apart]; decide, sa0, fun _ => ⟨by simp only [Apart, nA_eq]; decide,
          fun _ => by simp only [Apart, nA_eq]; decide⟩⟩
    | (intro h; exact absurd h (by decide))
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [LiveSep, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        rt_eq, outside_cons, outside_nil, and_true, SP0, HEAP, HEND, HSIZE, BUMP, WBUF]; omega)
    | (intro r hr; simp at hr; done)
    | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [rt_eq]
       simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | trivial
    | (intros; trivial)
    | (simp only [Apart, gA_eq, wbA_eq]; decide)
    | (intro _; simp only [Apart, gA_eq, wbA_eq]; decide)
    | (intro _; exact ⟨by simp only [Apart]; decide, fun _ => by simp only [Apart]; decide⟩)
    | (intro _; exact ⟨by simp only [Apart]; decide, by simp only [Apart, gA_eq]; decide⟩)
    | (intro _; exact ⟨by decide, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide),
        by rw [acc0]; decide +kernel, by decide⟩)
    | (intro _; simp only [outside_cons, outside_nil, and_true]; exact ⟨by decide, by simp only [Apart]; decide⟩)
    | (simp only [GuardOK, StackOK, acc0]; decide +kernel)
    | (decide +kernel)
    | (rw [acc0]; decide +kernel)
    | (simp only [NatNorm]; decide +kernel)
    | (simp only [Globals, RunIface.Globals, gA_eq, wbA_eq]; decide +kernel)
    | (simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide)
    | (simp only [StkOK, NatLive, Held, InRanges, outside_cons, outside_nil, and_true, rt_eq, acc0, stW0, stLen0,
        stCap0]; decide +kernel)
    | (simp only [NatLive, Held, InRanges, outside_cons, outside_nil, and_true, rt_eq, acc0]; decide +kernel)
    | skip

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, the call `z.modularInverseModPowerOfTwo(stk, 3, 64)` with a 2-word `z` and the stack
`{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (H B : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program ModInv.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n] s ∧
    ModInv.PreQ R NatSqr.sqrWX H sqrCQ mulCQ B L zp zl zc st xp xl xc n s ∧
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
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ ModInv.PostQ R NatSqr.sqrWX H sqrCQ mulCQ B L zp zc st xp xl n s s' :=
  ⟨WStubs.impl, R, 80, BW, [], ZP, 0, 2, ST, XP, 1, 1, 64, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _, hret, setup _ args (by decide), pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] (by intro t ht; simp at ht) _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] (by intro t ht; simp at ht) _) 80 BW [] ZP 0 2 ST XP 1 1 64
      RET hret s0 (setup _ args (by decide)) pre⟩

end FvModexp.Arm64.ModInvRow.Witness
