import FvModexp.Proofs.Arm64.Exp.W4P01Defs

/-!
# W4P01Defs's segment proofs (split out of `W4P01Defs` in s67 so that modules needing only `W4P01Defs`'s definitions do not wait
for these proofs; unchanged text, same namespace)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

set_option maxHeartbeats 64000000 in
/-- everything `p01 → powHead` establishes, from the two montgomery posts -/
theorem p01post {R : RtInv} {L : List (Nat × Nat)} {b g sp n mp t bp onep rrp xp : Nat} {M M1 M2 : Memory}
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (ht : t < 2 ^ 64) (hm : Inp R L sp n M mp)
    (hbb : bp + 8 * (17 * n) ≤ 2 ^ 48) (hbh : InRanges bp (8 * (17 * n)) L ∨ Outside bp (8 * (17 * n)) R.rt)
    (hbw : Apart bp (8 * (17 * n)) (sp - 4288) (4288 + 1040)) (hbm : Apart bp (8 * (17 * n)) mp (8 * n))
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * (17 * n)) onep (8 * n))
    (hrr : Inp R L sp n M rrp) (hbr : Apart bp (8 * (17 * n)) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * (17 * n)) xp (8 * n))
    (v1 : M1.readLE bp (8 * n) = Exp.montgomery n
      (((((M.writeLE (sp + 248) 8 (17 * n)).writeLE (sp + 824) 8 bp).writeLE (sp + 312) 8 (n + n * 2)).writeLE
        (sp + 224) 8 (18446744073709551616 - t)).readLE onep (8 * n))
      (((((M.writeLE (sp + 248) 8 (17 * n)).writeLE (sp + 824) 8 bp).writeLE (sp + 312) 8 (n + n * 2)).writeLE
        (sp + 224) 8 (18446744073709551616 - t)).readLE rrp (8 * n))
      (((((M.writeLE (sp + 248) 8 (17 * n)).writeLE (sp + 824) 8 bp).writeLE (sp + 312) 8 (n + n * 2)).writeLE
        (sp + 224) 8 (18446744073709551616 - t)).readLE mp (8 * n))
      ((18446744073709551616 - t) % 18446744073709551616))
    (i1 : R.inv b L g (view R.rt L M1))
    (F1 : MemFrame ((((M.writeLE (sp + 248) 8 (17 * n)).writeLE (sp + 824) 8 bp).writeLE (sp + 312) 8 (n + n * 2)).writeLE
      (sp + 224) 8 (18446744073709551616 - t)) M1 (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++
        [(bp, bp + 8 * (2 * n))]))
    (L1 : LiveFrame ((((M.writeLE (sp + 248) 8 (17 * n)).writeLE (sp + 824) 8 bp).writeLE (sp + 312) 8 (n + n * 2)).writeLE
      (sp + 224) 8 (18446744073709551616 - t)) M1 L [(bp, bp + 8 * (2 * n))])
    (g1 : M1.regions = M.regions)
    (v2 : M2.readLE (bp + 8 * n) (8 * n) = Exp.montgomery n
      ((((M1.writeLE (sp + 432) 8 bp).writeLE (sp + 440) 8 n).writeLE (sp + 448) 8 (2 * n)).readLE xp (8 * n))
      ((((M1.writeLE (sp + 432) 8 bp).writeLE (sp + 440) 8 n).writeLE (sp + 448) 8 (2 * n)).readLE rrp (8 * n))
      ((((M1.writeLE (sp + 432) 8 bp).writeLE (sp + 440) 8 n).writeLE (sp + 448) 8 (2 * n)).readLE mp (8 * n))
      ((18446744073709551616 - t) % 18446744073709551616))
    (i2 : R.inv b L g (view R.rt L M2))
    (F2 : MemFrame (((M1.writeLE (sp + 432) 8 bp).writeLE (sp + 440) 8 n).writeLE (sp + 448) 8 (2 * n)) M2
      (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(bp + 8 * n, bp + 8 * n + 8 * (2 * n))]))
    (L2 : LiveFrame (((M1.writeLE (sp + 432) 8 bp).writeLE (sp + 440) 8 n).writeLE (sp + 448) 8 (2 * n)) M2 L
      [(bp + 8 * n, bp + 8 * n + 8 * (2 * n))])
    (g2 : M2.regions = M1.regions) :
    FQ R L sp bp (17 * n) M (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)) ∧
    R.inv b L g (view R.rt L
      (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n))) ∧
    (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)).regions = M.regions ∧
    (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)).readLE (sp + 224) 8 =
      (2 ^ 64 - t) % 2 ^ 64 ∧
    (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)).readLE (sp + 248) 8 =
      17 * n ∧
    (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)).readLE (sp + 824) 8 =
      bp ∧
    Ent sp n bp (fun _ => Exp.montgomery n (M.readLE onep (8 * n)) (M.readLE rrp (8 * n)) (M.readLE mp (8 * n))
      ((2 ^ 64 - t) % 2 ^ 64))
      (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)) 0 ∧
    Ent sp n bp (fun _ => Exp.montgomery n (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) (M.readLE mp (8 * n))
      ((2 ^ 64 - t) % 2 ^ 64))
      (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)) 1 := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have od := OneIn.disj hone
  have u1 := hbw; have u2 := hbm; have u3 := hbo; have u4 := hbr; have u5 := hbx
  have w1 := hm.2.2.2; have w2 := hrr.2.2.2; have w3 := hx.2.2.2
  unfold Apart at u1 u2 u3 u4 u5 w1 w2 w3
  have e2 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have fq : FQ R L sp bp (17 * n) M
      (((M2.writeLE (sp + 456) 8 (bp + 8 * n)).writeLE (sp + 464) 8 n).writeLE (sp + 472) 8 (2 * n)) := by
    repeat (first
      | exact ⟨MemFrame.refl _ _, LiveFrame.refl _ _ _⟩
      | refine FQ.write ?_ hLs _ (by omega)
      | refine FQ.call ?_ F2 L2 ⟨by omega, by omega⟩
      | refine FQ.call ?_ F1 L1 ⟨by omega, by omega⟩)
  refine ⟨fq, ?_, by simp only [Memory.regions_writeLE, g2, g1], ?_, ?_, ?_, ?_, ?_⟩
  · repeat (first | exact i2 | refine FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) ?_)
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [rd_call F2 hwrt hsp1 (by omega) (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [rd_call F1 hwrt hsp1 (by omega) (by omega) (by omega), rd_self8, e2]
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [rd_call F2 hwrt hsp1 (by omega) (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [rd_call F1 hwrt hsp1 (by omega) (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact rd_w8 rfl (by omega)
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [rd_call F2 hwrt hsp1 (by omega) (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [rd_call F1 hwrt hsp1 (by omega) (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact rd_w8 rfl (by omega)
  · -- entry 0
    have hh0 : InRanges bp (8 * n) L ∨ Outside bp (8 * n) R.rt :=
      hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
    simp only [Ent, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      rw [FvModexp.Expmc.held_readLE hh0 F2 L2 (by simp only [outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      rw [v1, e2]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    all_goals
      try simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      rw [rd_call F2 hwrt hsp1 (by omega) (by omega) (by omega)]
      try simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      exact rd_w8 (by omega) (by omega)
  · -- entry 1
    have hx1 : InRanges xp (8 * n) L ∨ Outside xp (8 * n) R.rt := hx.2.2.1
    have hr1 : InRanges rrp (8 * n) L ∨ Outside rrp (8 * n) R.rt := hrr.2.2.1
    have hm1 : InRanges mp (8 * n) L ∨ Outside mp (8 * n) R.rt := hm.2.2.1
    simp only [Ent, Nat.one_mul, Nat.mul_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      rw [v2, e2]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      rw [FvModexp.Expmc.held_readLE hx1 F1 L1 (by simp only [outside_cons, outside_nil, and_true]; omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega),
        FvModexp.Expmc.held_readLE hr1 F1 L1 (by simp only [outside_cons, outside_nil, and_true]; omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega),
        FvModexp.Expmc.held_readLE hm1 F1 L1 (by simp only [outside_cons, outside_nil, and_true]; omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      exact rd_w8 (by omega) (by omega)
    · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      exact rd_w8 (by omega) (by omega)
    · exact rd_w8 (by omega) (by omega)

end FvModexp.Arm64.W4Pro
