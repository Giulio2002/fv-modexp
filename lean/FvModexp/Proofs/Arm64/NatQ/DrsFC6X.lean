import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFC6
import FvModexp.Proofs.Arm64.NatQ.DrsFC6R

/-! (Q-form copy of Arm64/Nat/DrsFC6X.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final correction loop: after `addTo(u[s:], v[s:])` (natdiv.go:876 → 869)

`c6xF`: from `addTo`'s return `0x1babcc` (`BxF` at `corrOnce stb`): `JMP` → the back edge `0x1baaa4` (`c6rF`) → the
head `CF (i + 1)` with the invariant `BxF.next`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c6xF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFA2)
    (hbx : BxF R c s Lk bk T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb))
    (k : ∀ S', CF R c s Lk bk S' j Z U qv (i + 1) (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hsp := hbx.sp; have h28 := hbx.r28; have h29 := hbx.r29; have h18 := hbx.r18
  have hinv := BxF.next hbx.hi hbx.pos hbx.inv
  have hB : Box (BxF R c s Lk bk T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb)) := ⟨hbx⟩
  clear hbx
  janus_run until [cBackF]
  exact c6rF impl R c s Lk bk j Z U qv i _ Q _ rfl rfl h28 h29 h18 hB.1.mc hB.1.v3 hB.1.si hB.1.hi hinv k

end FvModexp.Arm64.Q.DivRec
