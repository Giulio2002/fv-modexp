import FvModexp.Proofs.Amd64.NatQ.DrsSegD
import FvModexp.Proofs.Amd64.NatQ.DrsFC6R

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC2B.lean; adapted from Amd64/NatQ/DrsC2B.lean)
# `divRecursiveStep` (amd64), final correction loop: `if e > 0 { … }` (natdiv.go:871)

`c2bF`: from `nat.cmp`'s return (`0x5f03bc`, `RAX = ofInt (cmpQ |PF| st)`; `TESTQ AX, AX; JLE 0x5f0335`): `e ≤ 0` →
the back edge (`c6rF`, invariant by `CF.skip`); `e > 0` → the loads of `qhat` (`AX = DI = 0x148(SP')` ptr,
`BX = SI = 0xb8(SP')` len, `CX = R8 = 0xa8(SP')` cap, `R9 = 1`) → `CALL subVW(qhat, qhat, 1)` (`0x5f03f0`, return
`0x5f03f5`) with `BxF` (base state = the head's) at the pre-call state.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the correction test** after the final loop's `nat.cmp` -/
theorem c2bF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St) (Q : State → Prop)
    (hi : i < 2) (hinv : Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length (2 - i) st = c.sFF s U)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rFC1) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.PF s U).length st))
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv3 : V3F c s T.mem qv (c.PF s U).length)
    (hsi : T.mem.readLE ((s.regs 4).toNat - 184) 8 = i)
    (kC : ∀ S', CF R c s Lk bk S' j Z U qv (i + 1) st → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (kY : ∀ Y : State, BxF R c s Lk bk T j Z U qv i st st →
      Y.rip = BitVec.ofNat 64 SubVW.entry → Y.regs 4 = s.regs 4 - 400#64 → Y.regs 5 = s.regs 4 - 8#64 →
      Y.regs 14 = s.regs 14 → Y.fsBase = s.fsBase → Y.df = false → Y.xmm 15 = 0#128 →
      Y.regs 0 = BitVec.ofNat 64 c.t0 → Y.regs 3 = BitVec.ofNat 64 (c.qF s U).length →
      Y.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1) → Y.regs 7 = BitVec.ofNat 64 c.t0 →
      Y.regs 6 = BitVec.ofNat 64 (c.qF s U).length → Y.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      Y.regs 9 = 1#64 → MemFrame T.mem Y.mem (isR s) → Y.mem.regions = T.mem.regions →
      Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rFW1 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hB : Box (McF R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  have hB4 : Box (V3F c s T.mem qv (c.PF s U).length) := ⟨hv3⟩
  have r4 := hmc.bd.sl.q0p; have r5 := hmc.q3.s200; have r6 := hmc.bd.sl.q0c
  rcases natCmp_range (st.buf.take (c.PF s U).length) (Mdl.norm st.w) with he | he | he
  · -- e = -1: no correction
    have hle : Mdl.cmpQ (c.PF s U).length st ≤ 0 := by show Mdl.natCmp _ _ ≤ 0; rw [he]; decide
    have h0' : T.regs 0 = 18446744073709551615#64 := by
      rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hinv' := CF.skip hi hle hinv
    clear hmc hv3 h0 kY
    janus64_run [h0', BitVec.msb_eq_decide] until [cBackF]
    exact c6rF impl R c s Lk bk j Z U qv i st Q _ rfl hsp h5 h14 hfs rfl hx15 hB.h hB4.h hsi hi hinv' kC
  · -- e = 0: no correction
    have hle : Mdl.cmpQ (c.PF s U).length st ≤ 0 := by show Mdl.natCmp _ _ ≤ 0; rw [he]; decide
    have h0' : T.regs 0 = 0#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hinv' := CF.skip hi hle hinv
    clear hmc hv3 h0 kY
    janus64_run [h0', BitVec.msb_eq_decide] until [cBackF]
    exact c6rF impl R c s Lk bk j Z U qv i st Q _ rfl hsp h5 h14 hfs rfl hx15 hB.h hB4.h hsi hi hinv' kC
  · -- e = 1: correct
    have hpos : 0 < Mdl.cmpQ (c.PF s U).length st := by show 0 < Mdl.natCmp _ _; rw [he]; decide
    have h0' : T.regs 0 = 1#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hBx : BxF R c s Lk bk T j Z U qv i st st := ⟨hsp, h5, h14, hfs, hdf, hx15, hB.h, hB4.h, hsi, hi, hpos, hinv⟩
    have hBB : Box (BxF R c s Lk bk T j Z U qv i st st) := ⟨hBx⟩
    clear hmc hv3 h0 kC hBx
    janus64_run [r4, r5, r6, h0', BitVec.msb_eq_decide] until [SubVW.entry]
    refine kY _ hBB.h rfl ?_ ?_ ?_ hfs rfl hx15 ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by unfold isR; janus_frame)
      (by janus64_simp) ?_
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]); (try rw [hsp])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]); (try exact h5)
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]); (try exact h14)
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    · dsimp only
      (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
