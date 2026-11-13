import FvModexp.Proofs.Arm64.Exp.P2W2Fin


/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `return z.setWord(1)` / `return nat{1}` (nat.go:1187-1192) (agent infra)

From `r1E` (`0x1b6674`, the skip loop found `y mod 2^(logM-1) = 0`):
* `r1a`: `z ≠ nil`, `cap z ≠ 0`: `z[0] = 1`, `z = z[:1]`, the inline `norm` (one word) → `tB`;
* `r1b`: `z ≠ nil`, `cap z = 0`: `makeslice(Word, 1, 1)`, `[0] = 1` → `tB`;
* `r1c`: `z == nil`: `newobject([1]Word)`, `[0] = 1` → `tN`.
Each ends with the closure + `RET` (`P2W2Tail`) and the post `FQ` with value `1` (`finQ`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.ExpHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z ≠ nil`, `cap z ≠ 0`: `z[0] = 1` in place -/
theorem r1a {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm (stLen s.mem st))
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {cst : Nat} (hb : b - cst ≤ b1)
    (hzp : zp ≠ 0) (hzc : 0 < zc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1795700) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h7 : S.regs 7 = 1#64) (hm : S.mem = M) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S (FQ R b L K zp zc st 1 cst s) := by
  obtain ⟨⟨hzO1, hzO2, hzO3, -⟩, hzacc, hz48, hz8, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hzc
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hzc40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, r472, r488, -⟩ := hsl
  have hzaM : M.accessible zp 8 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hwacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [hw.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hzO2 hzO3
  subst hm
  janus_run [r472, r488, hzaM] until [tB]
  have hF1 : MemFrame S.mem (S.mem.writeLE zp 8 1) [(zp, zp + 8)] :=
    (MemFrame.refl _ _).writeLE_inRanges _ ⟨(zp, zp + 8), by simp, by simp only; omega, by simp only; omega⟩
  have hzH : InRanges zp (8 * zc) L1 ∨ Outside zp (8 * zc) R.rt := hw.le.held hzO1
  have hw' : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem (S.mem.writeLE zp 8 1) L1 b1 ℓ := by
    refine hw.frame hF1 (by simp only [Memory.regions_writeLE]) (fun a k ho => ?_) (fun a k _ ho => ?_) ?_ ?_
    · simp only [ZS, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [ZS, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show zp + 8 - zp = 8 by omega]
      exact hzH.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega))
  have hsl' : ESl (S.mem.writeLE zp 8 1) sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm
      (stLen s.mem st) :=
    ESl.keep hsl0 (fun a k ha => Memory.readLE_writeLE_of_disjoint _ _ (by omega)) (by omega)
  have hres : NatOF R L L1 (S.mem.writeLE zp 8 1) zp zc 1 zp 1 zc 1 := by
    refine ⟨?_, Or.inr ?_, by omega, hzc40, fun _ => ⟨hz8, hzH, ?_, hz48⟩, Or.inl ⟨rfl, rfl⟩⟩
    · show (S.mem.writeLE zp 8 1).readLE zp (8 * 1) = 1
      rw [Memory.readLE_writeLE_self]
    · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Memory.readLE_writeLE_self]; decide
    · simp only [Memory.accessible_writeLE]; rw [hw.fr.accessible]; exact hzacc
  rw [show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
  refine tailB hap _ _ sp g st (stLen s.mem st) zp 1 zc (s.regs 30).toNat (s.regs 18) (s.regs 29)
    (S.mem.writeLE zp 8 1) rfl rfl ?_ ?_ ?_ ?_ ?_ rfl (by omega) (by omega) (by omega) (tenv_of hP hw' hsl' hr4 hr48)
    (fun s' ht => finQ hP hw' hres (rs_z hP hw') hb ht)
  all_goals janus_simp

end

end FvModexp.Arm64.P2W2
