import FvModexp.Proofs.Amd64.NatQ.DrsSegD
import FvModexp.Proofs.Amd64.NatQ.DrsFC6R

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC6X.lean)
# `divRecursiveStep` (amd64), final correction loop: after `addTo(u[s:], v[s:])` (natdiv.go:877 → 869)

`c6xF`: from `addTo`'s return `0x5f0505` (`BxF` at `corrOnce stb`): `JMP` → the back edge `0x5f0335` (`c6rF`) → the
head `CF (i + 1)` with the invariant `BxF.next`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c6xF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rFA)
    (hbx : BxF R c s Lk bk T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb))
    (k : ∀ S', CF R c s Lk bk S' j Z U qv (i + 1) (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hsp := hbx.sp; have h5 := hbx.r5; have h14 := hbx.r14; have hfs := hbx.fs; have hdf := hbx.df
  have hx15 := hbx.x15
  have hinv := BxF.next hbx.hi hbx.pos hbx.inv
  have hB : Box (BxF R c s Lk bk T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb)) :=
    ⟨hbx⟩
  clear hbx
  janus64_run until [cBackF]
  exact c6rF impl R c s Lk bk j Z U qv i _ Q _ rfl hsp h5 h14 hfs rfl hx15 hB.h.mc hB.h.v3 hB.h.si hB.h.hi hinv k

end FvModexp.Amd64.Q.DivRec
