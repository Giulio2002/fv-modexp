import Janus
import Extracted
import FvModexp.Spec.Pool

set_option autoImplicit false

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1b): amd64 definitions the row-1 statements of
`(*bigModExp).Run` use for the Janus `sync.(*Pool)` contracts: the pooled element type `stkT` (byte-identical copy of
the proof-side `FvModexp.Amd64.Free.stkT`, Proofs/Amd64/Nat/Free.lean; shown equal by `rfl`). The witness call-site
premises `mvSite`/`mkSite`/`noSite` (amd64 twins of `Spec.WitSitesArm64`'s, copies of `Amd64.AsmWit`'s; used by the
row-1 error witness); the others are added with the amd64 success witness. -/

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

end FvModexp.Spec.WitSitesAmd64
