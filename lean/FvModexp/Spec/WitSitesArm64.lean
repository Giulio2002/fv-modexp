import Janus
import Extracted
import FvModexp.Spec.Pool

set_option autoImplicit false

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1b): the arm64 call-site premises the row-1 WITNESS
statement (`RunSucc.Witness.nonvacuous`) exhibits, one state per Janus runtime contract of `(*bigModExp).Run`. Each is
the conjunction of the contract's own precondition parts (Janus `…Pre`, `StackRoom`, `LiveAt`/`LiveMemAt`, `LiveDest`) at
a call; they are byte-identical reducible copies of the proof-side witness defs (`FvModexp.Arm64.AsmWit.{mvSite, mkSite}`
Proofs/Arm64/Witness/AsmWit.lean, `{clSite, wbSite, grSite}` Witness/Sites.lean, `{noSite, getSite, putSite}`
Int/ModRowW.lean, `Free.stkT` Nat/Free.lean); the proofs show each equal to its copy by `rfl`. -/

namespace FvModexp.Spec.WitSitesArm64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- the `*big.stack` type descriptor (read-only data of the extraction): the `Pool.Put` element type -/
abbrev stkT : Nat := Extracted.dataAddr.«type:*big.stack#6bae7c96»

/-- the premise of `MemmoveLive` (and of the other live copy contracts) at a call -/
@[reducible] def mvSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  Mem.EqPre 4096 3 s ∧
  LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
  Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
  LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat

/-- the premise of `MakesliceLiveContract` at a call -/
@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
      (s.regs 28).toNat s.mem (calleeStack s 4096 3)

/-- the premise of `MemclrNoHeapPointersLive` at a call -/
@[reducible] def clSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  Mem.EqPre 4096 2 s ∧
  LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s 4096 2) ∧
  LiveDest R L s 4096 2 (s.regs 0).toNat (s.regs 1).toNat

/-- the premise of `WbLiveContract … n` at a call -/
@[reducible] def wbSite (R : RtInv) (addr n : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s 4096 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    LiveSep L [(s.sp.toNat - 4096, s.sp.toNat - 8)] ∧ LiveSep [(s.sp.toNat - 4096, s.sp.toNat - 8)] R.rt

/-- the premise of `GrowsliceLiveContract` at a call -/
@[reducible] def grSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
    LiveAt R addr (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 5)

/-- the premise of `NewobjectLiveContract` at a call -/
@[reducible] def noSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1)

/-- the premise of `PoolGetLive` at a call -/
@[reducible] def getSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s 4096 1 ∧ StackRoom s 4096 1 ∧ s.mem.readLE ((s.regs 0).toNat + Pool.newOffset) 8 = 0 ∧
    LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s 4096 1)

/-- the premise of `PoolPutLive … stkT StkShape` at a call -/
@[reducible] def putSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat))
    (s : State) : Prop :=
  CallOK s 4096 3 ∧ StackRoom s 4096 3 ∧ (s.regs 1).toNat = stkT ∧ StkShape s.mem (s.regs 2).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧ LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s 4096 3)

end FvModexp.Spec.WitSitesArm64
