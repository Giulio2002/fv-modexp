import FvModexp.Proofs.Amd64.NatQ.DrsFRel3
import FvModexp.Proofs.Amd64.NatQ.DrsNormF

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF3.lean `f3n`/`f3x`/`nf3_mk`; adapted from Amd64/NatQ/DrsB3N.lean)
# `divRecursiveStep` (amd64), final block segment 3a: `qhat = qhat.norm()`, `CALL (*stack).nat(3n)` (natdiv.go:864-865)

`f3n`: from `AF2` (`0x5f0233`): `RAX = qhat0`, `RBX = B + 1`, the inlined `norm()` loop (`normF2`), `f3x`: its exit
`0x5f0258` → `len ≤ cap` check, `MOVQ BX, 0xb8(SP)` (`r-208`), `RBX = 3n`, `RAX = stk` → `CALL (*stack).nat` at
`0x5f0285` (`NF3` at the callee entry; no `mark` in the final block).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the own stores of segment 3a: the return slot of the call and `len(qhat)` -/
@[reducible] def isF3 (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392), ((s.regs 4).toNat - 208, (s.regs 4).toNat - 200)]

set_option maxHeartbeats 16000000 in
/-- `N3` from `A2` and the stores (pure) -/
theorem nf3_mk {R : RtInv} {c : Cx} {s S X : State} {Lk : List (Nat × Nat)} {bk j qn : Nat} {Z U : List Nat}
    (hA : AF2 R c s Lk bk S j Z U)
    (hpc : X.rip = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.st) (h3 : X.regs 3 = BitVec.ofNat 64 (3 * c.vl))
    (hF2 : MemFrame S.mem X.mem (isF3 s)) (hreg : X.mem.regions = S.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rF3n)
    (e1 : X.mem.readLE ((s.regs 4).toNat - 208) 8 = qn)
    (hqle : qn ≤ c.vl / 2 + 1) (hqv : natVal S.mem c.t0 qn = natVal S.mem c.t0 (c.vl / 2 + 1))
    (hqN : NatNorm S.mem c.t0 qn) : NF3 R c s Lk bk X j Z U qn := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame S.mem X.mem (fw s) := hF2.mono fun x n ho => by
    simp only [fw, win, isF3, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF2.readLE _ _ (by simp only [win, isF3, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → X.mem.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  refine ⟨hpc, hsp, h5, h14, hfs, hdf, hx15, h0, h3, hra, hcr, Ev.own hcr hA.ev hF hreg, Fp.own hcr hA.fp hF,
    hA.bd.frame hF2 (by simp only [FixOut, isF3, outside_cons, outside_nil, and_true]; omega)
      (by simp only [FOut, isF3, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw), hA.jB, hA.li,
    by rw [limbs_congr (rt _ _ (Nat.le_refl _) (Nat.le_refl _))]; exact hA.qk,
    by rw [limbs_congr (rd _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk, hqle, ?_, ?_, ⟨e1⟩,
    bud_cap (Cr.capOwn hcr hF) hA.bud⟩
  · show X.mem.readLE c.t0 (8 * qn) = X.mem.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [rt _ _ (Nat.le_refl _) (by omega), rt _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hqv
  · rcases hqN with h | h
    · exact Or.inl h
    · right; rw [rt _ _ (by omega) (by omega)]; exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from the exit of `qhat.norm()` (`0x5efc59`) to `CALL (*stack).nat(3n)` -/
theorem f3x (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (S : State) (j : Nat) (Z U : List Nat) (hA : AF2 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ X qn, NF3 R c s Lk bk X j Z U qn → ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q)
    (P : State) (n' : Nat) (hpc : P.rip = BitVec.ofNat 64 nExF2) (hm : P.mem = S.mem)
    (h3 : P.regs 3 = BitVec.ofNat 64 n') (hsp : P.regs 4 = s.regs 4 - 392#64) (h5 : P.regs 5 = s.regs 4 - 8#64)
    (h14 : P.regs 14 = s.regs 14) (hfs : P.fsBase = s.fsBase) (hdf : P.df = false) (hx15 : P.xmm 15 = 0#128)
    (hle : n' ≤ c.vl / 2 + 1)
    (hv : natVal S.mem c.t0 n' = natVal S.mem c.t0 (c.vl / 2 + 1)) (hN : NatNorm S.mem c.t0 n') :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hspS : (P.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have e400 : (s.regs 4 - 400#64).toNat = (s.regs 4).toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hA.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hst48 : c.st + 24 ≤ 2 ^ 48 := hA.ev.sok.2.2.2.1
  have haccT : S.mem.accessible c.st 24 true = true := hA.ev.sok.2.2.1
  have r1 : S.mem.readLE ((s.regs 4).toNat - 224) 8 = c.vl / 2 + 1 := hsl.q0c
  have r2 : S.mem.readLE ((s.regs 4).toNat - 192) 8 = c.vl := hsl.nn
  have r3 : S.mem.readLE ((s.regs 4).toNat + 56) 8 = c.st := hsl.s4
  have hlt : (BitVec.ofNat 64 (c.vl / 2 + 1) < BitVec.ofNat 64 n') = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have hst : BitVec.ofNat 64 c.st + 8#64 = BitVec.ofNat 64 (c.st + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsto : Outside c.st 24 (win s c.W 96) := hpre.sti.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hsto
  have had : BitVec.ofNat 64 c.vl + BitVec.ofNat 64 c.vl <<< 1 = BitVec.ofNat 64 (3 * c.vl) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  janus64_run [hm, r1, r2, r3, hlt, had, BitVec.msb_eq_decide] until [segAddr Extracted.program StackNat.fn]
  refine k _ n' (nf3_mk hA rfl ?sp ?r5 ?r14 hfs rfl hx15 ?r0 ?r3 (by unfold isF3; janus_frame) (by janus64_simp) ?ra ?e1
    hle hv hN)
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  case e1 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **segment 3a**: `A2` → `qhat.norm()` → `CALL (*stack).nat(3n)` -/
theorem f3n (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (S : State) (j : Nat) (Z U : List Nat) (hA : AF2 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ X qn, NF3 R c s Lk bk X j Z U qn → ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hpc := hA.pc; have hsp := hA.sp
  have hspS : (S.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hA.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hsl.q0p; have r2 := hsl.q0l
  janus64_run [r1, r2] until [nHdF2]
  have hacc : S.mem.accessible c.t0 (8 * (c.vl / 2 + 1)) false = true := by
    rw [hA.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_read_of_write _ hcr.t0acc
  refine normF2 impl (retAddrOf s) S.mem c.t0 (c.vl / 2 + 1) (natVal S.mem c.t0 (c.vl / 2 + 1)) _ Q ?_ (by omega)
    hcr.t048 hacc ?_ (c.vl / 2 + 1) _ (Nat.le_refl _) rfl ?_ ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩ rfl rfl
  · intro P n' hpc' hm' h3' hS' hle' hv' hN'
    refine f3x impl R c s Lk bk S j Z U hA Q k P n' hpc' hm' h3' ?_ ?_ ?_ ?_ ?_ ?_ hle' hv' hN'
    · rw [hS'.1 4 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
    · rw [hS'.1 5 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hA.r5
    · rw [hS'.1 14 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hA.r14
    · rw [hS'.2.1]; exact hA.fs
    · rw [hS'.2.2.1]; exact hA.df
    · rw [hS'.2.2.2]; exact hA.x15
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])

end FvModexp.Amd64.Q.DivRec
