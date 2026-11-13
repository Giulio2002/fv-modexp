import FvModexp.Proofs.Amd64.NatQ.DrsC2

set_option autoImplicit false

/-! (amd64 twin (asm s49) of Arm64/NatQ/DrsC2B.lean)
# `divRecursiveStep` (amd64), correction loop: `if e <= 0 { break }` (natdiv.go:834)

`c2b`: from `nat.cmp`'s return (`0x5efdf9`, `RAX = ofInt (cmpQ |P| st)`; `TESTQ AX, AX; JLE 0x5f072c`): `e ≤ 0` →
`0x5f072c` (reload `AX, CX, BX = qhatv`; `JMP 0x5eff2e`) → the exit `E` (the state is final by `C.brk`); `e > 0` →
the loads of `qhat` (`AX = DI = 0x148(SP')` ptr, `BX = SI = 0xc0(SP')` len, `CX = R8 = 0xa8(SP')` cap, `R9 = 1`) →
`CALL subVW(qhat, qhat, 1)` (`0x5efe30`, return `0x5efe35`) with `Bx` (base state = the head's) at the pre-call state.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

-- (ISA-free; copied from Arm64/NatQ/DrsC2.lean)
theorem cmpInt_range (a b : Nat) : Mdl.cmpInt a b = -1 ∨ Mdl.cmpInt a b = 0 ∨ Mdl.cmpInt a b = 1 := by
  unfold Mdl.cmpInt; split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

theorem cmpRev_range : ∀ (a b : List Nat), Mdl.cmpRev a b = -1 ∨ Mdl.cmpRev a b = 0 ∨ Mdl.cmpRev a b = 1
  | [], _ => by simp [Mdl.cmpRev]
  | [a], [] => by simp [Mdl.cmpRev]
  | [a], [b] => by simp only [Mdl.cmpRev]; exact cmpInt_range a b
  | [a], _ :: _ :: _ => by simp [Mdl.cmpRev]
  | _ :: _ :: _, [] => by simp [Mdl.cmpRev]
  | _ :: _ :: _, [_] => by simp [Mdl.cmpRev]
  | a :: a' :: xs, b :: b' :: ys => by
    simp only [Mdl.cmpRev]; split
    · exact cmpRev_range (a' :: xs) (b' :: ys)
    · exact cmpInt_range a b

theorem natCmp_range (x y : List Nat) : Mdl.natCmp x y = -1 ∨ Mdl.natCmp x y = 0 ∨ Mdl.natCmp x y = 1 := by
  unfold Mdl.natCmp; split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  · exact cmpRev_range _ _

/-- `subVW(qhat, qhat, 1)`'s return address -/
abbrev rW1 : Nat := 0x5efe35

/-- the return slot of a loop call -/
@[reducible] def isR (s : State) : List (Nat × Nat) := [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the break test** after the loop's `nat.cmp` -/
theorem c2b (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St) (Q : State → Prop)
    (hi : i < 2) (hinv : Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length (2 - i) st =
      Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rC1) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st))
    (hmc : Mc R c s Lk bk T.mem j Z U qv st) (hv4 : V4 c s T.mem qv (c.P s j U).length)
    (hsi : T.mem.readLE ((s.regs 4).toNat - 176) 8 = i)
    (kE : ∀ S', E R c s Lk bk S' j Z U qv → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (kY : ∀ Y : State, Bx R c s Lk bk T j Z U qv i st st →
      Y.rip = BitVec.ofNat 64 SubVW.entry → Y.regs 4 = s.regs 4 - 400#64 → Y.regs 5 = s.regs 4 - 8#64 →
      Y.regs 14 = s.regs 14 → Y.fsBase = s.fsBase → Y.df = false → Y.xmm 15 = 0#128 →
      Y.regs 0 = BitVec.ofNat 64 c.t0 → Y.regs 3 = BitVec.ofNat 64 (c.q0 s j U).length →
      Y.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1) → Y.regs 7 = BitVec.ofNat 64 c.t0 →
      Y.regs 6 = BitVec.ofNat 64 (c.q0 s j U).length → Y.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      Y.regs 9 = 1#64 → MemFrame T.mem Y.mem (isR s) → Y.mem.regions = T.mem.regions →
      Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rW1 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hB : Box (Mc R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  have hB4 : Box (V4 c s T.mem qv (c.P s j U).length) := ⟨hv4⟩
  have r1 := hv4.s328; have r2 := hv4.s152; have r3 := hv4.s168
  have r4 := hmc.bd.sl.q0p; have r5 := hmc.q3.s208; have r6 := hmc.bd.sl.q0c
  rcases natCmp_range (st.buf.take (c.P s j U).length) (Mdl.norm st.w) with he | he | he
  · -- e = -1: break
    have hle : Mdl.cmpQ (c.P s j U).length st ≤ 0 := by show Mdl.natCmp _ _ ≤ 0; rw [he]; decide
    have h0' : T.regs 0 = 18446744073709551615#64 := by
      rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hfin := C.brk hi hle hinv
    clear hmc hv4 h0 kY
    janus64_run [r1, r2, r3, h0', BitVec.msb_eq_decide] until [cExit]
    refine kE _ ⟨rfl, ?sp, ?r5, ?r14, hfs, rfl, hx15, ?r0, ?r3, ?r1, hfin ▸ hB.h, hB4.h⟩
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals first | exact hsp | exact h5 | exact h14
  · -- e = 0: break
    have hle : Mdl.cmpQ (c.P s j U).length st ≤ 0 := by show Mdl.natCmp _ _ ≤ 0; rw [he]; decide
    have h0' : T.regs 0 = 0#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hfin := C.brk hi hle hinv
    clear hmc hv4 h0 kY
    janus64_run [r1, r2, r3, h0', BitVec.msb_eq_decide] until [cExit]
    refine kE _ ⟨rfl, ?sp, ?r5, ?r14, hfs, rfl, hx15, ?r0, ?r3, ?r1, hfin ▸ hB.h, hB4.h⟩
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals first | exact hsp | exact h5 | exact h14
  · -- e = 1: correct
    have hpos : 0 < Mdl.cmpQ (c.P s j U).length st := by show 0 < Mdl.natCmp _ _; rw [he]; decide
    have h0' : T.regs 0 = 1#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hBx : Bx R c s Lk bk T j Z U qv i st st := ⟨hsp, h5, h14, hfs, hdf, hx15, hB.h, hB4.h, hsi, hi, hpos, hinv⟩
    have hBB : Box (Bx R c s Lk bk T j Z U qv i st st) := ⟨hBx⟩
    clear hmc hv4 h0 kE hBx
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
