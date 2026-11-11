import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Ic

/-! `osakaModexpGas(baseLen, expLen, modLen, expHead)` (amd64, `RAX`, `RBX`, `RCX`, the head by value at `[RSP + 8, RSP + 40)`):
the result is `Geth.osakaModexpGas` of the arguments (GethGas.lean, a transcription of contracts.go:580-598). -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

abbrev ogA : Nat := segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.osakaModexpGas"

/-- The stack `osakaModexpGas` needs: its frame (`PUSH RBP; SUB $0x38`) and the return slot of the `modexpIterationCount` call below
`RSP`, the return address and the 32-byte head above it. -/
abbrev OgPre (s : State) : Prop :=
  RA s ∧ StackGuardOK s 0 ∧ StackWritable s 72 40 ∧
    ((s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16)

/-- The exponent head the caller passed (the four limbs at `RSP + 8`). -/
abbrev ogHead (s : State) : Nat :=
  L4 (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) (s.mem.readLE ((s.regs 4).toNat + 24) 8)
    (s.mem.readLE ((s.regs 4).toNat + 32) 8)

abbrev OgPost (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [BitVec.ofNat 64 (Geth.osakaModexpGas (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (ogHead s))]
      f x yh m zh kr ∧ MemFrame s.mem m [((s.regs 4).toNat - 72, (s.regs 4).toNat)]

theorem rd16_lo (m : Memory) (a : Nat) : m.readLE a 16 / 1 % 18446744073709551616 = m.readLE a 8 := by
  rw [Nat.div_one, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  have := Janus.Arm64.Memory.readLE_lt m a 8
  simp only [Nat.reducePow] at this ⊢
  omega

theorem rd16_hi (m : Memory) (a : Nat) : m.readLE a 16 / 18446744073709551616 = m.readLE (a + 8) 8 := by
  rw [show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  have := Janus.Arm64.Memory.readLE_lt m a 8
  simp only [Nat.reducePow] at this ⊢
  omega

theorem toNat0 : (0 : BitVec 64).toNat = 0 := rfl

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- `osakaModexpGas` from `+0x6c` (the multiplication complexity `mc` is in `RAX`, the frame is set up) to its return. -/
theorem og_tail (s : State) (R : Nat → W64) (F : Flags)
    (hR3 : R 3 = s.regs 3) (hR4 : R 4 = s.regs 4 - 64#64) (hR5 : R 5 = s.regs 4 - 8#64) (hR14 : R 14 = s.regs 14)
    (hpre : OgPre s) :
    ReachesRet Extracted.program (retAddrOf s)
      { s with regs := R, rip := BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.osakaModexpGas" + 0x6c)),
               flags := F, mem := s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat }
      (fun s' => ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
        s' = retState64 s junk [BitVec.ofNat 64 (Geth.osakaTail (R 0).toNat (s.regs 3).toNat (ogHead s))] f x yh m zh kr ∧
        MemFrame s.mem m [((s.regs 4).toNat - 72, (s.regs 4).toNat)]) := by
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  janus64_run [hR3, hR4, hR5, hR14] calls [ic_summary]
  all_goals first
    | (exfalso; omega)
    | (refine Ret64.ret_intro0 rfl rfl rfl (by simp only [callRegs64_apply, setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false, hR14, false_or, or_true]) rfl rfl rfl rfl rfl rfl ?_ rfl rfl (by janus_frame)
       simp only [getD_cons_zero]
       apply BitVec.eq_of_toNat_eq
       janus64_simp
       simp only [rd16_lo, rd16_hi, Nat.add_assoc, Nat.reduceAdd] at *
       have hic := Geth.iterationCount_lt (s.regs 3).toNat (ogHead s)
       unfold ogHead at hic
       unfold Geth.osakaTail Geth.maxU64
       simp only [BitVec.toNat_ofNat, Nat.reducePow, apply_ite BitVec.toNat, toNat0] at *
       have hc : (R 0).toNat < 18446744073709551616 := (R 0).isLt
       generalize Geth.iterationCount _ _ 16 = IC at *
       generalize (R 0).toNat = c at *
       try simp only [Nat.mod_eq_of_lt hic] at *
       generalize IC * c = P at *
       try dsimp only
       repeat' split
       all_goals first
         | omega
         | ((try simp only [BitVec.toNat_ofNat, Nat.reducePow] at *) <;> omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem og_summary : Summary Extracted.program ogA OgPre OgPost := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨⟨hra, hra2, hra3⟩, hg, ⟨hlow, hnw, hacc⟩, hdg⟩ := hpre'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hdg
  by_cases hmx : (s.regs 0).toNat < (s.regs 1).toNat
  all_goals janus64_run [hmx] until [ogA + 0x6c]
  all_goals first
    | (exfalso; omega)
    | (refine ReachesRet.mono (og_tail s _ _ (by simp only [setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false]) (by simp only [setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false]) (by simp only [setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false]) (by simp only [setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false]) hpre) ?_
       intro s' ⟨junk, f, x, yh, m, zh, kr, h1, h2⟩
       refine ⟨junk, f, x, yh, m, zh, kr, ?_, h2⟩
       rw [h1, Geth.osakaModexpGas_tail]
       refine congrArg (fun v => retState64 s junk [BitVec.ofNat 64 (Geth.osakaTail v (s.regs 3).toNat (ogHead s))] f x yh m zh kr) ?_
       simp only [setRegF_apply, Nat.reduceEqDiff, ite_true, ite_false]
       unfold Geth.osakaMultComplexity Geth.berlinMultComplexity Geth.maxU64
       simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow, apply_ite BitVec.toNat,
         toNat0, BitVec.toNat_add, BitVec.toNat_mul, Nat.reduceMod, Nat.zero_add] at *
       have hA := (s.regs 0).isLt; have hB := (s.regs 1).isLt
       generalize BitVec.toNat (s.regs 0) = a at *; generalize BitVec.toNat (s.regs 1) = b at *
       have hmv : (if ¬b < a ∧ ¬(18446744073709551616 - a + b) % 18446744073709551616 = 0 then b else a) = max a b := by
         rw [Nat.max_def]; split <;> split <;> omega
       simp only [hmv] at *
       have m1 := Nat.le_max_left a b; have m2 := Nat.le_max_right a b
       have m3 : max a b < 2 ^ 64 := by rw [Nat.max_def]; split <;> omega
       generalize max a b = mx at *
       simp only [Nat.reducePow, ite_eq_right_iff, Nat.one_ne_zero, imp_false, Nat.not_le] at *
       repeat' split
       all_goals first
         | omega
         | (try simp (disch := omega) only [Nat.mod_eq_of_lt] at *
            generalize (mx + 7) / 8 = w at *
            generalize w * w = W at *
            omega))

end FvModexp.Amd64.RG
