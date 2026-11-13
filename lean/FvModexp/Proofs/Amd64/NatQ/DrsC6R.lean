import FvModexp.Proofs.Amd64.NatQ.DrsC5R

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsC6R.lean)
# `divRecursiveStep` (amd64), correction loop: back to the head after one correction (natdiv.go:833)

`c6r`: from `addTo`'s return (`0x5efd85`, `Bx … stb (corrOnce …)`) → `DX = 0xd8(SP') + 1` (`i + 1`), `AX, CX, BX` =
`qhatv` (`0x140`, `0x98`, `0x88`) → the head `0x5efda8` with `C … (i + 1) (corrOnce …)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c6r (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rA)
    (hbx : Bx R c s Lk bk T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb))
    (k : ∀ S', C R c s Lk bk S' j Z U qv (i + 1) (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have hsp := hbx.sp; have h5 := hbx.r5; have h14 := hbx.r14; have hfs := hbx.fs; have hx15 := hbx.x15
  have hdf := hbx.df
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r0 := hbx.si; have r1 := hbx.v4.s328; have r2 := hbx.v4.s152; have r3 := hbx.v4.s168
  have hi := hbx.hi
  have hinv := Bx.next hi hbx.pos hbx.inv
  have hB1 : Box (Mc R c s Lk bk T.mem j Z U qv (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb)) :=
    ⟨hbx.mc⟩
  have hB2 : Box (V4 c s T.mem qv (c.P s j U).length) := ⟨hbx.v4⟩
  have e3 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  clear hbx hmc hpre hcr
  janus64_run [r0, r1, r2, r3, e3] until [cHead]
  refine k _ ⟨rfl, ?sp, ?r5, ?r14, hfs, rfl, hx15, ?r0, ?r3, ?r1, ?r2, hB1.h, hB2.h, by omega, hinv⟩
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case sp => exact hsp
  case r5 => exact h5
  case r14 => exact h14

end FvModexp.Amd64.Q.DivRec
