import FvModexp.Proofs.Amd64.NatQ.RemDefs
import FvModexp.Proofs.Amd64.Nat.Restore
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.DivmcBits

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): after `div` — the result slots, the deferred `stk.restore(stk.save())` closure
(`CALL CX`), the epilogue and `RET` (twin of Arm64/NatQ/RemFin.lean; divmc s58)

`dsum`: the closure `nat.rem.deferwrap1` as a summary on `LibRem` (`Restore.Pre`/`Restore.Post`; the one-`janus64_run`
proof of Amd64/NatQ/BasicSqrDfr.lean). `fin`: from `div`'s return `0x5ede0a` (`RSP = r - 200`) to `rem`'s return.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem.deferwrap1"

set_option maxRecDepth 20000 in
theorem dsum (impl : List Amd64.Segment) :
    Summary (LibRem.program.link impl) (segAddr LibRem.program fnD) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnD, reduceSegAddr] at hpc
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

/-- the writes after `div`'s return: the result slots, the defer bit, the closure call's frame, `len(stk.w)` -/
@[reducible] def finW (s : State) (st : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 89, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 72, (s.regs 4).toNat - 48),
    ((s.regs 4).toNat - 216, (s.regs 4).toNat - 200), (st + 8, st + 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from `div`'s return through the closure call and the epilogue to `rem`'s return** -/
theorem fin (impl : List Amd64.Segment) (s U : State) (zp zl zc st up ul uc r rl rc : Nat)
    (hpc : U.rip = BitVec.ofNat 64 (callDiv + 5)) (hsp : U.regs 4 = s.regs 4 - 200#64)
    (h14 : U.regs 14 = s.regs 14) (hfs : U.fsBase = s.fsBase)
    (hdf : U.df = false)
    (e7 : U.regs 7 = BitVec.ofNat 64 r) (e6 : U.regs 6 = BitVec.ofNat 64 rl) (e8 : U.regs 8 = BitVec.ofNat 64 rc)
    (hsl : Sl s zp zl zc st up ul uc U.mem)
    (hal : (s.regs 4).toNat % 8 = 0) (hb : 41720 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (hw : U.mem.accessible ((s.regs 4).toNat - 41720) (41720 + 112) true = true)
    (hstacc : U.mem.accessible st 24 true = true) (hst48 : st + 24 ≤ 2 ^ 48)
    (hsw : st + 24 ≤ (s.regs 4).toNat - 41720 ∨ (s.regs 4).toNat + 112 ≤ st)
    (hcap : stLen s.mem st ≤ stCap U.mem st) (hr : r < 2 ^ 64) (hrl : rl < 2 ^ 64) (hrc : rc < 2 ^ 64)
    (hra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ReachesRet (LibRem.program.link impl) (retAddrOf s) U (fun s' =>
      (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = U.xmm 15) ∧
      s'.fsBase = s.fsBase ∧ s'.df = U.df ∧
      s'.regs 0 = BitVec.ofNat 64 r ∧ s'.regs 3 = BitVec.ofNat 64 rl ∧ s'.regs 1 = BitVec.ofNat 64 rc ∧
      MemFrame U.mem s'.mem (finW s st) ∧ s'.mem.readLE (st + 8) 8 = stLen s.mem st) := by
  have m1 := hsl.ra; have m2 := hsl.bp; have mdp := hsl.dp
  have mdf : U.mem.readLE ((s.regs 4).toNat - 40) 8 = 6217440 := hsl.dfn
  have f8 : U.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = st := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact hsl.dst
  have f16 : U.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 = stLen s.mem st := by
    rw [show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega]; exact hsl.dn
  have mcap : U.mem.readLE (st + 16) 8 = stCap U.mem st := rfl
  have hD := dsum impl
  have eD : segAddr LibRem.program fnD = 6217440 := by decide
  rw [eD] at hD
  have hraccE : U.mem.accessible ((s.regs 4).toNat - 32) 16 false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  have hwaccE : U.mem.accessible ((s.regs 4).toNat - 224) 16 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hraR : U.mem.accessible ((s.regs 4).toNat - 8) 16 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hsl
  janus64_run [m1, m2, mdp, mdf, mcap, f8, f16, e7, e6, e8, mod64_of_lt ((s.regs 4).toNat - 40) (by omega)] calls [hD]
  janus_grab 208 as hFF
  have hfs2 : s'.fsBase = U.fsBase := by janus_assumption
  refine ⟨hfs2.trans hfs, ?_⟩
  refine MemFrame.trans (?A : MemFrame U.mem _ (finW s st)) hFF fun a n ho => ⟨ho, ?_⟩
  · unfold finW; janus_frame
  · simp only [finW, outside_cons, outside_nil, and_true] at ho ⊢
    janus64_simp
    omega

end FvModexp.Amd64.Q.NatRem
