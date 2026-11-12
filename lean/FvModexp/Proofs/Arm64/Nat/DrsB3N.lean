import FvModexp.Proofs.Arm64.Nat.DrsA3

/-!
# `divRecursiveStep` (arm64), loop body segment 3a: `qhat = qhat.norm()`, `mark`, → `CALL (*stack).nat(3n)`

`b3n`: from `A2` (`0x1ba614`, after the recursive call) → `qhat.norm()` (`norm3`, natdiv.go:828) → `len(qhat)` spilled at
`SP'+208`, `mark = stk.len` at `SP'+256` (natdiv.go:829) → `CALL (*stack).nat(3n)` (`N3`), via the continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the own stores of segment 3a -/
@[reducible] def is2 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 192, s.sp.toNat - 184), (s.sp.toNat - 144, s.sp.toNat - 136)]

set_option maxHeartbeats 16000000 in
/-- `N3` from `A2` and the two stores (pure) -/
theorem n3_mk {R : RtInv} {c : Cx} {s S X : State} {Lk : List (Nat × Nat)} {bk j qn : Nat} {Z U : List Nat}
    (hA : A2 R c s Lk bk S j Z U)
    (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.st) (h1 : X.regs 1 = BitVec.ofNat 64 (3 * c.vl))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 r3n) (hF2 : MemFrame S.mem X.mem (is2 s)) (hreg : X.mem.regions = S.mem.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 192) 8 = qn) (e2 : X.mem.readLE (s.sp.toNat - 144) 8 = c.l1 s)
    (hqle : qn ≤ c.vl / 2 + 1) (hqv : natVal S.mem c.t0 qn = natVal S.mem c.t0 (c.vl / 2 + 1))
    (hqN : NatNorm S.mem c.t0 qn) : N3 R c s Lk bk X j Z U qn := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame S.mem X.mem (fw s) := hF2.mono fun x n ho => by
    simp only [fw, winA, is2, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF2.readLE _ _ (by simp only [win, is2, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → X.mem.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  refine ⟨hpc, hsp, h28, h29, h18, h0, h1, h30, hcr, Ev.own hcr hA.ev hF hreg, Fp.own hcr hA.fp hF,
    hA.bd.frame hF2 (by simp only [FixOut, is2, outside_cons, outside_nil, and_true]; omega)
      (by simp only [IOut, is2, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw),
    hA.bs.frame hF2 (by simp only [BOut, is2, outside_cons, outside_nil, and_true]; omega), hA.jB, hA.li,
    by rw [limbs_congr (rt _ _ (Nat.le_refl _) (Nat.le_refl _))]; exact hA.qk,
    by rw [limbs_congr (rd _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk, hqle, ?_, ?_, ⟨e1, e2⟩, hA.bud⟩
  · show X.mem.readLE c.t0 (8 * qn) = X.mem.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [rt _ _ (Nat.le_refl _) (by omega), rt _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hqv
  · rcases hqN with h | h
    · exact Or.inl h
    · right; rw [rt _ _ (by omega) (by omega)]; exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from the exit of `qhat.norm()` (`0x1ba640`) to `CALL (*stack).nat(3n)` -/
theorem b3x (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State)
    (j : Nat) (Z U : List Nat) (hA : A2 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ X qn, N3 R c s Lk bk X j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q)
    (P : State) (n' : Nat) (hpc : P.pc = BitVec.ofNat 64 nExit3) (hm : P.mem = S.mem)
    (h1 : P.regs 1 = BitVec.ofNat 64 n') (hsp : P.sp = s.sp - 400#64) (h28 : P.regs 28 = s.regs 28)
    (h29 : P.regs 29 = s.sp - 408#64) (h18 : P.regs 18 = s.regs 18) (hle : n' ≤ c.vl / 2 + 1)
    (hv : natVal S.mem c.t0 n' = natVal S.mem c.t0 (c.vl / 2 + 1)) (hN : NatNorm S.mem c.t0 n') :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hst48 : c.st + 24 ≤ 2 ^ 48 := hA.ev.sok.2.2.2.1
  have haccT : S.mem.accessible c.st 24 true = true := hA.ev.sok.2.2.1
  have r1 : S.mem.readLE (s.sp.toNat - 216) 8 = c.vl / 2 + 1 := hsl.q0c
  have r2 : S.mem.readLE (s.sp.toNat - 184) 8 = c.vl := hsl.nn
  have r3 : S.mem.readLE (s.sp.toNat + 32) 8 = c.st := hsl.s4
  have r4 : S.mem.readLE (c.st + 8) 8 = c.l1 s := hA.fp.len
  have hn1 : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hn2 : (BitVec.ofNat 64 (c.vl / 2 + 1)).toNat = c.vl / 2 + 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsh : BitVec.ofNat 64 c.vl <<< 1 = BitVec.ofNat 64 (2 * c.vl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have had : BitVec.ofNat 64 (2 * c.vl) + BitVec.ofNat 64 c.vl = BitVec.ofNat 64 (3 * c.vl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have had' : BitVec.ofNat 64 c.vl + BitVec.ofNat 64 (2 * c.vl) = BitVec.ofNat 64 (3 * c.vl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hst : BitVec.ofNat 64 c.st + 8#64 = BitVec.ofNat 64 (c.st + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus_run [r1, r2, r3, r4, hn1, hn2, hsh, had, hst] until [segAddr Extracted.program StackNat.fn]
  refine k _ n' (n3_mk hA rfl rfl ?_ ?_ ?_ ?_ ?_ rfl (by rw [← hm]; unfold is2; janus_frame) (by rw [← hm]; simp) ?_ ?_ hle hv hN)
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact had'
  · exact h28
  · exact h29
  · exact h18
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · have hsto : Outside c.st 24 (win s c.W 96) := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
    simp only [win, outside_cons, outside_nil, and_true] at hsto
    rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), r4]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **segment 3a**: `A2` → `qhat.norm()` → `CALL (*stack).nat(3n)` -/
theorem b3n (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State)
    (j : Nat) (Z U : List Nat) (hA : A2 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ X qn, N3 R c s Lk bk X j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hpc := hA.pc; have hsp := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hsl.q0p; have r2 := hsl.q0l
  janus_run [r1, r2] until [nHead3]
  have hacc : S.mem.accessible c.t0 (8 * (c.vl / 2 + 1)) false = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_read_of_write _ hcr.t0acc
  refine norm3 impl (s.regs 30) S.mem c.t0 (c.vl / 2 + 1) (natVal S.mem c.t0 (c.vl / 2 + 1)) _ Q ?_ (by omega)
    hcr.t048 hacc ?_ (c.vl / 2 + 1) _ (Nat.le_refl _) rfl ?_ rfl (fun _ _ _ _ => rfl) rfl rfl
  · intro P n' hpc' hm' h1' hsp' hS' hle' hv' hN'
    refine b3x impl R c s Lk bk S j Z U hA Q k P n' hpc' hm' h1' (by rw [hsp']) ?_ ?_ ?_ hle' hv' hN'
    · rw [hS' 28 (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
    · rw [hS' 29 (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h29
    · rw [hS' 18 (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])

end FvModexp.Arm64.DivRec
