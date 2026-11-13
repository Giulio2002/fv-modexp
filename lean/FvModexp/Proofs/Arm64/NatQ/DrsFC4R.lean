import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFC3
import FvModexp.Proofs.Arm64.NatQ.DrsC4R

/-! (Q-form copy of Arm64/Nat/DrsFC4R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final correction loop: to `CALL subVV.abi0(qhatv[:s], qhatv[:s], v[:s])` (natdiv.go:872)

`c4rF`: from `subVW(qhat)`'s return `0x1bab30`: the `s ≤ cap(qhatv)` check (`BCC` panic excluded), the nine argument
words `SP'+8 … SP'+72` → `CALL subVV.abi0` (`0x1bab60`, return `0x1bab64`). Adapted from DrsC4R.
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

/-- `subVV.abi0`'s return address in the final block -/
abbrev rFVV : Nat := 0x1bab64

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c4rF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFW1) (hbx : BxF R c s Lk bk T j Z U qv i stb st)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 subVVA → X.regs 30 = BitVec.ofNat 64 rFVV →
      X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 →
      MemFrame T.mem X.mem (isA s) → X.mem.regions = T.mem.regions →
      X.mem.readLE (s.sp.toNat - 392) 8 = qv → X.mem.readLE (s.sp.toNat - 384) 8 = c.vl / 2 - 1 →
      X.mem.readLE (s.sp.toNat - 368) 8 = qv → X.mem.readLE (s.sp.toNat - 344) 8 = c.vp →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsp := hbx.sp; have h28 := hbx.r28; have h29 := hbx.r29; have h18 := hbx.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hbx.v3.s160; have r2 := hmc.bd.ss; have r3 := hbx.v3.s320
  have r4 := hmc.bd.sl.s8; have r5 := hmc.bd.sl.s10
  have hqv : qv < 2 ^ 48 := by have := Memory.accessible_bound _ hmc.qa; omega
  have hvp : c.vp < 2 ^ 48 := by have := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1; omega
  obtain ⟨e1, e2, e3, e4⟩ := rd9 T.mem s.sp.toNat qv (c.vl / 2 - 1) (3 * c.vl) qv (c.vl / 2 - 1) (3 * c.vl) c.vp
    (c.vl / 2 - 1) c.vc (by omega) (by omega) (by omega) (by omega) (by omega)
  clear hbx hmc
  janus_run [r1, r2, r3, r4, r5] until [subVVA]
  refine k _ rfl rfl rfl ?_ ?_ ?_ (by unfold isA; janus_frame) (by simp) e1 e2 e3 e4
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18

end FvModexp.Arm64.Q.DivRec
