import FvModexp.Proofs.Amd64.NatQ.DrsFCE
import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC6R.lean; adapted from Amd64/NatQ/DrsC6R.lean)
# `divRecursiveStep` (amd64), final correction loop: the back edge (natdiv.go:869)

`c6rF`: from `0x5f0335` (reached by `JLE` after a non-positive `nat.cmp` and by `JMP` after `addTo`) →
`DX = 0xd0(SP') + 1` (`i + 1`), `AX, CX, BX` = `qhatv` (`0x138`, `0x90`, `0x80`) → the head `0x5f0360` with `CF (i + 1)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the back edge of the final correction loop -/
abbrev cBackF : Nat := 0x5f0335

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the back edge**: `i++` → `CF (i + 1)` at the model state `st` -/
theorem c6rF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 cBackF) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv3 : V3F c s T.mem qv (c.PF s U).length)
    (hsi : T.mem.readLE ((s.regs 4).toNat - 184) 8 = i) (hi : i < 2)
    (hinv : Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length (2 - (i + 1)) st = c.sFF s U)
    (k : ∀ S', CF R c s Lk bk S' j Z U qv (i + 1) st → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r0 := hsi; have r1 := hv3.s320; have r2 := hv3.s144; have r3 := hv3.s160
  have hB1 : Box (McF R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  have hB2 : Box (V3F c s T.mem qv (c.PF s U).length) := ⟨hv3⟩
  have e3 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  clear hmc hv3 hpre hcr
  janus64_run [r0, r1, r2, r3, e3] until [cHeadF]
  refine k _ ⟨rfl, ?sp, ?r5, ?r14, hfs, rfl, hx15, ?r0, ?r3, ?r1, ?r2, hB1.h, hB2.h, by omega, hinv⟩
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case sp => exact hsp
  case r5 => exact h5
  case r14 => exact h14

end FvModexp.Amd64.Q.DivRec
