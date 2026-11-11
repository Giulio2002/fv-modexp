import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Ic

/-! `osakaModexpGas` (arm64): `og_any` (returns, for every input) and `og_bounded` (lengths at most 1024: the result is the `Nat` model). -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

abbrev OgPre (s : State) : Prop :=
  LR s ∧ GuardOK s 0 ∧ StackOK s 88 40 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 128

/-- The `L4` value of the four limbs at `a`. -/
abbrev L4at (m : Memory) (a : Nat) : Nat := L4 (m.readLE a 8) (m.readLE (a + 8) 8) (m.readLE (a + 16) 8) (m.readLE (a + 24) 8)

theorem dmod0 (p : Prop) [Decidable p] : (decide p).toNat % 18446744073709551616 = 0 ↔ ¬ p := by
  by_cases h : p <;> simp [h]

theorem toNat0 : (0 : BitVec 64).toNat = 0 := rfl

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- `osakaModexpGas` from `+0x74` (the multiplication complexity is in `X2`) to its return. -/
theorem og_tail (s : State) (R : Nat → W64) (F : Flags) (pc : W64) (hpc : pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.osakaModexpGas" + 0x74)))
    (hR1 : R 1 = s.regs 1) (hR18 : R 18 = s.regs 18) (hR28 : R 28 = s.regs 28) (hR29 : R 29 = s.sp - 88#64)
    (hpre : OgPre s) :
    ReachesRet Extracted.program (s.regs regLR)
      { s with regs := R, sp := s.sp - 80#64, pc := pc, flags := F,
               mem := (s.mem.writeLE (s.sp.toNat - 80) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 88) 8 (s.regs 29).toNat }
      (fun s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
        s' = retStateX s junk [BitVec.ofNat 64 (Geth.osakaTail (R 2).toNat (s.regs 1).toNat
          (L4 (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) (s.mem.readLE (s.sp.toNat + 24) 8)
            (s.mem.readLE (s.sp.toNat + 32) 8)))] f v m ex ep ∧ MemFrame s.mem m [(s.sp.toNat - 88, s.sp.toNat)]) := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdg⟩ := hpre
  simp only [Disjoint] at hdg
  subst hpc
  janus_run [hR1, hR18, hR28, hR29] calls [ic_summary]
  all_goals first
    | (exfalso; omega)
    | (refine Ret.retX_intro0 rfl rfl (by simp [callRegs, setReg, hR18]) (by simp [callRegs, setReg, hR28]) (by simp [setReg]) rfl rfl rfl rfl (fun i hi => ?_) (by janus_frame)
       simp at hi; subst hi
       apply BitVec.eq_of_toNat_eq
       janus_simp
       have hic := Geth.iterationCount_lt (s.regs 1).toNat (L4 (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
         (s.mem.readLE (s.sp.toNat + 24) 8) (s.mem.readLE (s.sp.toNat + 32) 8))
       unfold Geth.osakaTail Geth.maxU64
       simp only [addWithCarry, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
         Bool.toNat_false, Nat.add_zero, Nat.zero_mod, toNat0, show (500#64).toNat = 500 from rfl, apply_ite BitVec.toNat] at *
       have hc : (R 2).toNat < 18446744073709551616 := (R 2).isLt
       generalize Geth.iterationCount _ _ 16 = IC at *
       generalize (R 2).toNat = c at *
       try simp only [Nat.mod_eq_of_lt hic] at *
       generalize IC * c = P at *
       try dsimp only
       repeat' split
       all_goals first
         | omega
         | ((try simp only [show (500#64).toNat = 500 from rfl, BitVec.toNat_ofNat, Nat.reducePow] at *) <;> omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- `osakaModexpGas(baseLen, expLen, modLen, expHead)` (arm64): the result is `Geth.osakaModexpGas` of the arguments, the exponent head
being the four limbs the caller stored at `SP + 8`. -/
theorem og_summary : Summary Extracted.program ogA OgPre
    (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      s' = retStateX s junk [BitVec.ofNat 64 (Geth.osakaModexpGas (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat
          (L4 (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) (s.mem.readLE (s.sp.toNat + 24) 8)
            (s.mem.readLE (s.sp.toNat + 32) 8)))] f v m ex ep ∧ MemFrame s.mem m [(s.sp.toNat - 88, s.sp.toNat)]) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨⟨hr1, hr2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdg⟩ := hpre'
  simp only [Disjoint] at hdg
  by_cases hmx : (s.regs 0).toNat < (s.regs 2).toNat
  all_goals janus_run [hmx, rot3_mask] until [ogA + 0x74]
  all_goals first
    | (exfalso; omega)
    | (refine Ret.rr_mono (og_tail s _ _ _ rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) hpre) ?_
       intro s' ⟨junk, f, v, m, ex, ep, h1, h2⟩
       refine ⟨junk, f, v, m, ex, ep, ?_, h2⟩
       rw [h1, Geth.osakaModexpGas_tail]
       congr 4
       simp only [setReg, Nat.reduceEqDiff, ite_true, ite_false, if_true, if_false]
       unfold Geth.osakaMultComplexity Geth.berlinMultComplexity Geth.maxU64
       simp only [umulh2, addWithCarry, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_mul, BitVec.toNat_add,
         BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow, Bool.toNat_false, Nat.add_zero,
         Nat.zero_mod, toNat0, umulh_toNat, Janus.Arm64.addWithCarry_c64, Janus.Arm64.addWithCarry_fst_toNat, apply_ite BitVec.toNat] at *
       simp only [Nat.reduceMod, Nat.zero_add] at *
       try simp only [dmod0, ne_eq, Decidable.not_not] at *
       have hA := (s.regs 0).isLt; have hB := (s.regs 2).isLt
       first | rw [Nat.max_eq_right (by omega)] | rw [Nat.max_eq_left (by omega)]
       generalize BitVec.toNat (s.regs 0) = a at *; generalize BitVec.toNat (s.regs 2) = b at *
       repeat' split
       all_goals first
         | omega
         | (try simp (disch := omega) only [Nat.mod_eq_of_lt] at *
            generalize (b + 7) / 8 = w at *
            generalize w * w = W at *
            omega))

end FvModexp.Arm64.RG
