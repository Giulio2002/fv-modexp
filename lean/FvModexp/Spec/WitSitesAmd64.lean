import Janus
import Extracted
import FvModexp.Spec.Pool

set_option autoImplicit false

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1b): amd64 definitions the row-1 statements of
`(*bigModExp).Run` use for the Janus `sync.(*Pool)` contracts: the pooled element type `stkT` (byte-identical copy of
the proof-side `FvModexp.Amd64.Free.stkT`, Proofs/Amd64/Nat/Free.lean; shown equal by `rfl`). The witness call-site
premises, one per Janus runtime contract of `(*bigModExp).Run` (amd64 twins of `Spec.WitSitesArm64`'s): byte-identical
reducible copies of the proof-side witness defs (`FvModexp.Amd64.AsmWit.{mvSite, clSite}` Proofs/Amd64/Witness/AsmWit.lean,
`{noSite, wbSite, getSite, grSite}` Witness/Sites.lean, `mkSite` AsmWit.lean, `ModRowW.putSite` Int/ModRowW.lean, with
`stkT`/`StkShape` for `Free.stkT`/`StkSh`); the proofs show each equal to its copy by `rfl`. `mvSite`/`mkSite`/`noSite`
are used by the row-1 error witness, all of them by the row-1 success witness. -/

namespace FvModexp.Spec.WitSitesAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- the `*big.stack` type descriptor (read-only data of the extraction): the `Pool.Put` element type -/
abbrev stkT : Nat := Extracted.dataAddr.«type:*big.stack#6bae7c96»

/-- the premise of `MemmoveLive64` (and of the other live copy contracts) at a call (copy of `Amd64.AsmWit.mvSite`) -/
@[reducible] def mvSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MemPre64 4096 3 s ∧
  LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3) ∧
  MemAmd64.Input s 4096 3 (s.regs 3).toNat (s.regs 1).toNat ∧
  LiveDest64 R L s 4096 3 (s.regs 0).toNat (s.regs 1).toNat

/-- the premise of `MakesliceLiveContract64` at a call (copy of `Amd64.AsmWit.mkSite`) -/
@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MakeslicePre64 4096 s ∧ StackRoom64 s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (makesliceRound64 s)
      (s.regs 14).toNat s.mem (liveWin64 s 4096 3)

/-- the premise of `NewobjectLiveContract64` at a call (copy of `Amd64.AsmWit.noSite`) -/
@[reducible] def noSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre64 4096 s ∧ StackRoom64 s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 1)

/-- the premise of `MemclrNoHeapPointersLive64` at a call (copy of `Amd64.AsmWit.clSite`) -/
@[reducible] def clSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MemPre64 4096 2 s ∧
  LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat] L b s (liveWin64 s 4096 2) ∧
  LiveDest64 R L s 4096 2 (s.regs 0).toNat (s.regs 3).toNat

/-- the premise of `WbLiveContract64 … n` at a call (copy of `Amd64.AsmWit.wbSite`) -/
@[reducible] def wbSite (R : RtInv) (addr n : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK64 s 4096 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    LiveSep L [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] ∧
    LiveSep [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] R.rt

/-- the premise of `PoolAmd64.PoolGetLive` at a call (copy of `Amd64.AsmWit.getSite`) -/
@[reducible] def getSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK64 s 4096 1 ∧ StackRoom64 s 4096 1 ∧ s.mem.readLE ((s.regs 0).toNat + Pool.newOffset) 8 = 0 ∧
    LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s 4096 1)

/-- the premise of `GrowsliceLiveContract64` at a call (copy of `Amd64.AsmWit.grSite`) -/
@[reducible] def grSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  GrowslicePre64 4096 s ∧ StackRoom64 s 4096 5 ∧
    LiveAt R addr (growsliceArgs64 s) L b (growsliceRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 5)

/-- the premise of `PoolAmd64.PoolPutLive … stkT StkShape` at a call (copy of `Amd64.ModRowW.putSite`) -/
@[reducible] def putSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat))
    (s : State) : Prop :=
  CallOK64 s 4096 3 ∧ StackRoom64 s 4096 3 ∧ (s.regs 3).toNat = stkT ∧ StkShape s.mem (s.regs 1).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧ LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s 4096 3)

end FvModexp.Spec.WitSitesAmd64
