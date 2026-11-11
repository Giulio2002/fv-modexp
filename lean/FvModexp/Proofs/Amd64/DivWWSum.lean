import FvModexp.Proofs.Common.AsmDivNat
import FvModexp.Proofs.Common.AsmDivMath
import FvModexp.Proofs.Common.AsmEns64
import FvModexp.Proofs.Lib.DivWWAmd64

/-!
# `math/big.divWW(x1, x0, y, m Word) (q, r Word)` (go-bigmodexpfix `src/math/big/arith.go:273`, Go ABIInternal, amd64)

As arm64 (`Arm64/DivWWSum.lean`): `q = (x1*2^64 + x0) / y`, `r = (x1*2^64 + x0) % y` for `y != 0`, `x1 < y`,
`m = recipWord y`. Registers: `RAX = x1, RBX = x0, RCX = y, RDI = m`; results `RAX = q`, `RBX = r`. Frameless (only the
`RET` reads the return address at `[RSP]`); memory unchanged. `nlz` is `BSR` (`63 - clz`; the zero-source case is excluded
by `y != 0`), the shifts are masked `SHLQ`/`SHRQ` by `CL`. Proof: `divWW_summary` runs the normalisation (two paths:
`nlz = 0` and `nlz >= 1`) to `entry + 0x5e`, `head_to_tail` hands over to `tail` (the estimate `t1` and the two corrections;
three runs with the intermediate words generalised). Mathematics: `Common/AsmDivMath.lean` (shared with arm64).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec
open FvModexp.Lib.DivWWAmd64 (program entry)
namespace FvModexp.Amd64.DivWWSum

theorem tv (a b c : Nat) (hb : b < 18446744073709551616) :
    a / 18446744073709551616 + c + (decide (18446744073709551616 ≤ a % 18446744073709551616 + b)).toNat =
      (a + b) / 18446744073709551616 + c := by
  have h1 := Nat.div_add_mod a 18446744073709551616
  have h2 := Nat.mod_lt a (show 0 < 18446744073709551616 by decide)
  by_cases h : 18446744073709551616 ≤ a % 18446744073709551616 + b
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

theorem r_vals64 (X1 X0 : BitVec 64) (T d : Nat) (hle : d * T ≤ X1.toNat * 2 ^ 64 + X0.toNat)
    (hlt : X1.toNat * 2 ^ 64 + X0.toNat < d * T + 2 ^ 64 + d) (hd : d < 2 ^ 64) :
    (X0 - BitVec.ofNat 64 (T * d)).toNat = (X1.toNat * 2 ^ 64 + X0.toNat - d * T) % 2 ^ 64 ∧
    (subFlags X1 (BitVec.ofNat 64 (T * d / 18446744073709551616))
      (decide (X0.toNat < T * d % 18446744073709551616))).fst.toNat = (X1.toNat * 2 ^ 64 + X0.toNat - d * T) / 2 ^ 64 := by
  have hX1 := X1.isLt; have hX0 := X0.isLt
  rw [Nat.mul_comm d T] at hle hlt ⊢
  simp only [subFlags, BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize T * d = P at *
  generalize X1.toNat = a at *
  generalize X0.toNat = b at *
  have hc : ∀ P : Prop, [Decidable P] → (decide P).toNat = if P then 1 else 0 := by
    intro P _; by_cases h : P <;> simp [h]
  rw [hc]
  constructor
  · omega
  · split <;> omega

theorem qval (T : BitVec 64) (R X d ra : Nat) (hra : ra < 2 ^ 64)
    (hq1 : (if d ≤ ra then (if 2 ^ 64 ≤ R then T.toNat + 1 else T.toNat) + 1
      else (if 2 ^ 64 ≤ R then T.toNat + 1 else T.toNat)) = X / d) (hqlt : X / d < 2 ^ 64) :
    BitVec.ofNat 64 (if 2 ^ 64 ≤ R then 1 else 0) + T + BitVec.ofNat 64 (if d ≤ ra then 1 else 0) =
      BitVec.ofNat 64 (X / d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := T.isLt
  by_cases h1 : 2 ^ 64 ≤ R <;> by_cases h2 : d ≤ ra <;> simp only [h1, h2, if_true, if_false] at hq1 ⊢ <;> omega

theorem tail (s : State) (Q : State → Prop) (hpc : s.rip = BitVec.ofNat 64 (entry + 0x5e))
    (hd1 : 2 ^ 63 ≤ (s.regs 1).toNat) (hX1 : (s.regs 0).toNat < (s.regs 1).toNat)
    (hm : (s.regs 7).toNat = (2 ^ 128 - 1) / (s.regs 1).toNat - 2 ^ 64) (hs : (s.regs 6).toNat ≤ 63)
    (h9 : (s.regs 9).toNat = 64 - (s.regs 6).toNat)
    (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hacc : s.mem.accessible (s.regs 4).toNat 8 false = true)
    (hQ : ∀ s' : State,
      s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) / (s.regs 1).toNat) →
      s'.regs 3 = BitVec.ofNat 64 ((((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) % (s.regs 1).toNat) / 2 ^ (s.regs 6).toNat) →
      (∀ i, i ∉ [0, 1, 2, 3, 4, 7, 8, 9] → s'.regs i = s.regs i) → s'.regs 4 = s.regs 4 + 8#64 → s'.mem = s.mem →
      s'.rip = retAddrOf s → s'.xmm = s.xmm → s'.fsBase = s.fsBase → s'.df = s.df → Q s') :
    ReachesRet program (retAddrOf s) s Q := by
  have hX0 := (s.regs 3).isLt
  janus64_run until [entry + 0x79]
  rw [tv _ _ _ hX0]
  have hd2 := (s.regs 1).isLt
  have hX0' := (s.regs 3).isLt
  have hm' : (s.regs 7).toNat = (2 ^ 64 * 2 ^ 64 - 1) / (s.regs 1).toNat - 2 ^ 64 := by
    rw [hm]
  have hest := FvModexp.AsmDiv.estimate_gen (2 ^ 64) (s.regs 1).toNat (s.regs 0).toNat (s.regs 3).toNat (s.regs 7).toNat
    (((s.regs 7).toNat * (s.regs 0).toNat + (s.regs 3).toNat) / 2 ^ 64 + (s.regs 0).toNat) (by omega) (by omega) hd2 hX1
    hX0' hm' rfl
  generalize hT : BitVec.ofNat 64 (((s.regs 7).toNat * (s.regs 0).toNat + (s.regs 3).toNat) / 18446744073709551616 +
    (s.regs 0).toNat) = T
  janus64_run until [entry + 0x82]
  generalize hr0 : s.regs 3 - BitVec.ofNat 64 (T.toNat * (s.regs 1).toNat) = r0
  generalize hr1 : (subFlags (s.regs 0) (BitVec.ofNat 64 (T.toNat * (s.regs 1).toNat / 18446744073709551616))
    (decide ((s.regs 3).toNat < T.toNat * (s.regs 1).toNat % 18446744073709551616))).fst = r1
  have hTv : T.toNat = ((s.regs 7).toNat * (s.regs 0).toNat + (s.regs 3).toNat) / 2 ^ 64 + (s.regs 0).toNat := by
    rw [← hT, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hest.1
  obtain ⟨hr0v, hr1v⟩ := r_vals64 (s.regs 0) (s.regs 3) T.toNat (s.regs 1).toNat (by rw [hTv]; exact hest.2.1)
    (by have := hest.2.2; rw [hTv]; omega) hd2
  rw [hr0] at hr0v
  rw [hr1] at hr1v
  have hcor := FvModexp.AsmDiv.corrections (s.regs 1).toNat ((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) T.toNat hd1 hd2
    (by rw [hTv]; exact hest.2.1) (by rw [hTv]; exact hest.2.2)
  have hXd' : (s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat < (s.regs 1).toNat * 2 ^ 64 := by
    have e : ((s.regs 0).toNat + 1) * 2 ^ 64 ≤ (s.regs 1).toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hX1
    rw [Nat.add_mul] at e; omega
  have hqlt := Nat.div_lt_of_lt_mul hXd'
  have hTb := hest.2.2
  rw [← hTv] at hTb
  have hTa := hest.2.1
  rw [← hTv] at hTa
  generalize (s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat = X at *
  generalize hR : X - (s.regs 1).toNat * T.toNat = R at *
  generalize hra : (if r1.toNat = 0 then r0 else r0 - s.regs 1) = ra
  have hrav : ra.toNat = if 2 ^ 64 ≤ R then (R % 2 ^ 64 + 2 ^ 64 - (s.regs 1).toNat) % 2 ^ 64 else R % 2 ^ 64 := by
    rw [← hra]
    by_cases hz : r1.toNat = 0
    · rw [if_pos hz, if_neg (by omega), hr0v]
    · rw [if_neg hz, if_pos (by omega), BitVec.toNat_sub, hr0v]; omega
  have hc2 : ∀ P : Prop, [Decidable P] → (P ↔ (s.regs 1).toNat ≤ ra.toNat) →
      ((if P then (1#8) else 0#8).setWidth 32).setWidth 64 = BitVec.ofNat 64 (if (s.regs 1).toNat ≤ ra.toNat then 1 else 0) := by
    intro P _ hP; by_cases h : P
    · rw [if_pos h, if_pos (hP.mp h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h (hP.mpr h'))]; rfl
  have hc2' : ((s.regs 1).toNat < ra.toNat ∨ (18446744073709551616 - ra.toNat + (s.regs 1).toNat) % 18446744073709551616 = 0) ↔
      (s.regs 1).toNat ≤ ra.toNat := by have := ra.isLt; omega
  have hc1 : ((if r1.toNat = 0 then (0#8) else 1#8).setWidth 32).setWidth 64 = BitVec.ofNat 64 (if 2 ^ 64 ≤ R then 1 else 0) := by
    by_cases hz : r1.toNat = 0
    · rw [if_pos hz, if_neg (by omega)]; rfl
    · rw [if_neg hz, if_pos (by omega)]; rfl
  have hfin := hcor
  simp only at hfin
  rw [← hrav] at hfin
  obtain ⟨hq1, hq2⟩ := hfin
  have hv : (if (s.regs 1).toNat ≤ ra.toNat then ra - s.regs 1 else ra).toNat = X % (s.regs 1).toNat := by
    by_cases h2 : (s.regs 1).toNat ≤ ra.toNat
    · rw [if_pos h2, BitVec.toNat_sub]; rw [if_pos h2] at hq2; have := ra.isLt; omega
    · rw [if_neg h2]; rw [if_neg h2] at hq2; exact hq2
  have hlt : X % (s.regs 1).toNat / 2 ^ (s.regs 6).toNat < 2 ^ 64 := by
    have := Nat.mod_lt X (show 0 < (s.regs 1).toNat by omega)
    have := Nat.div_le_self (X % (s.regs 1).toNat) (2 ^ (s.regs 6).toNat)
    omega
  have e9 : (18446744073709551616 - (s.regs 9).toNat) % 64 = (s.regs 6).toNat := by omega
  have hra' := ra.isLt
  janus64_run
  all_goals
    refine hQ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      rw [hra, hc1]
      simp only [hc2']
      rw [hc2 _ Iff.rfl]
      exact qval T R X _ _ hra' hq1 hqlt
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      rw [hra]
      simp only [hc2', e9, if_pos (show (s.regs 6).toNat < 64 by omega),
        show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
      apply BitVec.eq_of_toNat_eq
      first
        | (rw [BitVec.toNat_ushiftRight, hv, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; done)
        | (rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, show (s.regs 6).toNat = 0 by omega, Nat.pow_zero,
            Nat.div_one]; done)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      obtain ⟨i0, i1, i2, i3, i4, i7, i8, i9⟩ := hi
      simp only [setRegF_apply, i0, i1, i2, i3, i4, i7, i8, i9, if_false]
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
    · rfl
    · exact (retAddrOf_eq s).symm
    · rfl
    · rfl
    · rfl

/-- the postcondition of the summary: `RAX = q`, `RBX = r`, return (`RET` pops the return address) -/
def Post (s s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8#64 ∧
  s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) / (s.regs 1).toNat) ∧
  s'.regs 3 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) % (s.regs 1).toNat) ∧
  (∀ i, i ∉ [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11] → s'.regs i = s.regs i) ∧ MemFrame s.mem s'.mem [] ∧
  s'.xmm = s.xmm ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df

theorem head_to_tail (s S : State) (hy : (s.regs 1).toNat ≠ 0) (hx : (s.regs 0).toNat < (s.regs 1).toNat)
    (hm : (s.regs 7).toNat = FvModexp.AsmDiv.recipWord (s.regs 1).toNat)
    (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hacc : s.mem.accessible (s.regs 4).toNat 8 false = true)
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x5e))
    (hS1 : (S.regs 1).toNat = (s.regs 1).toNat * 2 ^ Janus.Arm64.clzNat 64 (s.regs 1).toNat)
    (hS6 : (S.regs 6).toNat = Janus.Arm64.clzNat 64 (s.regs 1).toNat)
    (hS9 : (S.regs 9).toNat = 64 - Janus.Arm64.clzNat 64 (s.regs 1).toNat) (hS7 : S.regs 7 = s.regs 7)
    (hSX : (S.regs 0).toNat * 2 ^ 64 + (S.regs 3).toNat =
      ((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) * 2 ^ Janus.Arm64.clzNat 64 (s.regs 1).toNat)
    (hS0 : (S.regs 0).toNat < (S.regs 1).toNat)
    (hSr : ∀ i, i ∉ [0, 1, 2, 3, 6, 7, 8, 9, 10, 11] → S.regs i = s.regs i) (hSm : S.mem = s.mem)
    (hSx : S.xmm = s.xmm) (hSf : S.fsBase = s.fsBase) (hSd : S.df = s.df) :
    ReachesRet program (retAddrOf s) S (Post s) := by
  have hn := FvModexp.AsmDiv.clz_norm64 (s.regs 1).toNat hy (s.regs 1).isLt
  have h4 : S.regs 4 = s.regs 4 := hSr 4 (by simp)
  have hret : retAddrOf S = retAddrOf s := by simp only [retAddrOf_eq, h4, hSm]
  rw [← hret]
  refine tail S _ hpc ?_ hS0 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hS1]; exact hn.2.1
  · rw [hS7, hm, hS1]; rfl
  · rw [hS6]; exact hn.1
  · rw [hS9, hS6]
  · rw [h4, hSm]; exact hr
  · rw [h4, hSm]; exact hacc
  · intro s' e0 e1 hr' h4' hmem hp hx' hf hd
    rw [hSX, hS1] at e0
    rw [hSX, hS1, hS6] at e1
    obtain ⟨c, hc⟩ : ∃ c, c = Janus.Arm64.clzNat 64 (s.regs 1).toNat := ⟨_, rfl⟩
    rw [← hc] at e0 e1 hn hS1
    obtain ⟨X, hX⟩ : ∃ X, X = (s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat := ⟨_, rfl⟩
    obtain ⟨y, hyd⟩ : ∃ y, y = (s.regs 1).toNat := ⟨_, rfl⟩
    rw [← hX, ← hyd] at e0 e1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hp, hret]
    · rw [h4', h4]
    · rw [← hX, ← hyd, e0, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos c)]
    · rw [← hX, ← hyd, e1, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos c)]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [hr' i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega),
        hSr i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]
    · rw [hmem, hSm]; exact MemFrame.refl _ _
    · rw [hx', hSx]
    · rw [hf, hSf]
    · rw [hd, hSd]

theorem sha64 (a b : BitVec 64) (c : Nat) (h1 : 1 ≤ c) (h2 : c ≤ 63) (h : a.toNat * 2 ^ c < 2 ^ 64) :
    (a <<< c ||| b >>> (64 - c)).toNat = a.toNat * 2 ^ c + b.toNat / 2 ^ (64 - c) := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have hb : b.toNat / 2 ^ (64 - c) < 2 ^ c := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show 64 - c + c = 64 by omega]; exact b.isLt
  rw [FvModexp.AsmDiv.or_hi_comm _ _ _ hb]; omega

theorem shb64 (a : BitVec 64) (c : Nat) (h2 : c < 64) : (a <<< c).toNat = a.toNat * 2 ^ c % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- the callee summary of `divWW` (amd64) -/
theorem divWW_summary : Summary program entry
    (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
      (s.regs 1).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 1).toNat ∧
      (s.regs 7).toNat = FvModexp.AsmDiv.recipWord (s.regs 1).toNat)
    Post := by
  intro s hpc ⟨hr, hacc, hy, hx, hm⟩
  have hy0 : ((s.regs 1).toNat = 0) = False := by simp [hy]
  have hn := FvModexp.AsmDiv.clz_norm64 (s.regs 1).toNat hy (s.regs 1).isLt
  have hx0 := (s.regs 3).isLt
  janus64_run [hy0] until [entry + 0x5e]
  · have hc0 : Janus.Arm64.clzNat 64 (s.regs 1).toNat = 0 := by omega
    refine head_to_tail s _ hy hx hm hr hacc rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, reduceIte, hc0, Nat.pow_zero, Nat.mul_one]
    all_goals first
      | rfl
      | decide
      | exact hx
      | (intro i hi
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
         obtain ⟨i0, i1, i2, i3, i6, i7, i8, i9, i10, i11⟩ := hi
         simp only [i0, i1, i2, i3, i6, i7, i8, i9, i10, i11, if_false])
  · generalize hcd : Janus.Arm64.clzNat 64 (s.regs 1).toNat = c at *
    have hc1 : 1 ≤ c := by omega
    have hcnd : 18446744073709551616 - (18446744073709551553 + (63 - c)) < 64 := by omega
    have e1 : (18446744073709551615 - (63 - c)) % 64 = c := by omega
    have e2 : (18446744073709551553 + (63 - c)) % 64 = 64 - c := by omega
    simp only [hcnd, if_true, e1, e2, show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
      BitVec.allOnes_and]
    have hnorm := FvModexp.AsmDiv.normalise (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat c (by omega) hn.1
      hn.2.2 hx hx0
    have hxc : (s.regs 0).toNat * 2 ^ c < 2 ^ 64 := by
      have e : ((s.regs 0).toNat + 1) * 2 ^ c ≤ (s.regs 1).toNat * 2 ^ c := Nat.mul_le_mul_right _ hx
      rw [Nat.add_mul] at e; omega
    have ea := sha64 (s.regs 0) (s.regs 3) c hc1 hn.1 hxc
    have eb := shb64 (s.regs 3) c (by omega)
    have ec := shb64 (s.regs 1) c (by omega)
    refine head_to_tail s _ hy hx hm hr hacc rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl rfl rfl rfl
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, reduceIte, hcd]
    · rw [ec, Nat.mod_eq_of_lt hn.2.2]
    · apply Eq.symm; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    · simp only [BitVec.toNat_ofNat]; omega
    · rw [ea, eb]; exact hnorm.1
    · rw [ea, ec, Nat.mod_eq_of_lt hn.2.2]; exact hnorm.2.1
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      obtain ⟨i0, i1, i2, i3, i6, i7, i8, i9, i10, i11⟩ := hi
      simp only [i0, i1, i2, i3, i6, i7, i8, i9, i10, i11, if_false]

/-- the standalone contract: `divWW(x1, x0, y, m)` with `y != 0`, `x1 < y`, `m` the reciprocal of `y` returns
`(q, r)` = `((x1*2^64+x0) / y, (x1*2^64+x0) % y)` and leaves memory unchanged. -/
theorem ensures (x1 x0 y m : BitVec 64) :
    Ensures program entry [x1, x0, y, m]
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧ y.toNat ≠ 0 ∧ x1.toNat < y.toNat ∧
        m.toNat = FvModexp.AsmDiv.recipWord y.toNat)
      (fun s s' => results 2 s' =
          [BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) / y.toNat),
           BitVec.ofNat 64 ((x1.toNat * 2 ^ 64 + x0.toNat) % y.toNat)] ∧
        MemFrame s.mem s'.mem []) := by
  refine FvModexp.Asm.ensures_of_summary64 divWW_summary ?_ ?_
  · intro ret s hret hsu ⟨hacc, hy, hx, hm⟩
    have h0 : s.regs 0 = x1 := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = y := by have := hsu.args 2 (by simp); simpa using this
    have h7 : s.regs 7 = m := by have := hsu.args 3 (by simp); simpa using this
    have hr := hsu.ret
    simp only [Amd64.Program.withExit, Janus.Amd64.GoABI.regSP] at hr
    refine ⟨by rw [hr]; exact hret.user, hacc, ?_, ?_, ?_⟩
    · rw [h1]; exact hy
    · rw [h0, h1]; exact hx
    · rw [h7, h1]; exact hm
  · intro ret s s' hret hsu _ ⟨_, h4, e0, e3, hr, hf, hx, _, _⟩
    have h0 : s.regs 0 = x1 := by have := hsu.args 0 (by simp); simpa using this
    have h3 : s.regs 3 = x0 := by have := hsu.args 1 (by simp); simpa using this
    have h1 : s.regs 1 = y := by have := hsu.args 2 (by simp); simpa using this
    rw [h0, h3, h1] at e0 e3
    refine ⟨⟨h4, hr 5 (by simp), hr 14 (by simp), by rw [hx]⟩, ?_, hf⟩
    simp only [results, Janus.Amd64.GoABI.intArgRegs, List.take, List.map_cons, List.map_nil]
    rw [e0, e3]

end FvModexp.Amd64.DivWWSum
