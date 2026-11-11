import FvModexp.Proofs.Arm64.Exp.W4PowDefs

/-!
# window-4 prologue (arm64): `powers[0]`, `powers[1]` (nat.go:1413-1414) — definitions

From the return of `buf := stk.nat(17·numWords)` (pc `p01`, `+0x5ac`): `k0 = -k0'` stored, `powers[0] =
buf[0:n:2n].montgomery(one, RR, …)`, `powers[1] = buf[n:2n:3n].montgomery(x, RR, …)`, `i = 2`, jump to the table loop head.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the return address of `stk.nat(17·numWords)` -/
abbrev p01 : Nat := 1799964

/-- `one` (nat.go:1407): a held array apart from the window, or (`n ≤ 4`) the frame buffer `[sp + 336, sp + 368)` -/
@[reducible] def OneIn (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  Inp R L sp n M0 p ∨ (p = sp + 336 ∧ n ≤ 4)

/-- the input facts `MontW.MCall` needs of an operand (window `[sp - 4288, sp + 120)` only) -/
@[reducible] def InpC (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧
  Apart p (8 * n) (sp - 4288) (4288 + 120)

theorem Inp.c {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M0 : Memory} (h : Inp R L sp n M0 p) :
    InpC R L sp n M0 p := ⟨h.1, h.2.1, h.2.2.1, by have := h.2.2.2; unfold Apart at this ⊢; omega⟩

theorem OneIn.c {R : RtInv} {L : List (Nat × Nat)} {g sp n p : Nat} {M0 : Memory} (he : Env R L g sp M0)
    (h : OneIn R L sp n M0 p) : InpC R L sp n M0 p := by
  obtain ⟨hal, hsp1, hsp2, hwacc, -, -, -, hwrt, -, -, -⟩ := he
  rcases h with h | ⟨rfl, hn⟩
  · exact Inp.c h
  · exact ⟨M0.accessible_sub hwacc (Or.inr rfl) (by omega) (by omega), by omega,
      Or.inr (hwrt.of_sub (by omega) (by omega)), by unfold Apart; omega⟩

theorem mcall_ofC {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc rp rc xp yp : Nat} {M0 : Memory}
    (he : Env R L g sp M0) (hn : 0 < n) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hr : Buf R L g sp n M0 rp rc)
    (hx : InpC R L sp n M0 xp) (hy : InpC R L sp n M0 yp) (hm : Inp R L sp n M0 mp)
    (hrx : Apart rp (8 * rc) xp (8 * n)) (hry : Apart rp (8 * rc) yp (8 * n)) (hrm : Apart rp (8 * rc) mp (8 * n))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n]) :
    MontW.MCall R L g (M0.readLE (g + 16) 8) sp n mp mc rp rc xp yp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hr
  have sub : ∀ p k, Apart p k (sp - 4288) (4288 + 1040) → Apart p k (sp - 4288) (4288 + 120) := by
    intro p k h; unfold Apart at h; unfold Apart; omega
  refine ⟨h1, h2, by omega, h5, h7,
    h8.of_sub (Nat.le_refl _) (by omega), sub _ _ h9, h10, ?_, hn, r1, r2, hmc, hmc', r4, r5, sub _ _ r6, r7,
    ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, hy.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, hok.1, hok.2⟩
  intro r hr
  have := h11 r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- the frame words `p01 → powHead` writes besides `buf` (callee window, `k0`, `len(buf)`, `3n`, headers 0-1, `&buf`) -/
@[reducible] def qw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4288, sp - 8), (sp + 8, sp + 120), (sp + 224, sp + 232), (sp + 248, sp + 256), (sp + 312, sp + 320),
    (sp + 432, sp + 480), (sp + 824, sp + 832)]

@[reducible] def FQ (R : RtInv) (L : List (Nat × Nat)) (sp bp bc : Nat) (M0 M : Memory) : Prop :=
  MemFrame M0 M (R.rt ++ qw sp ++ [(bp, bp + 8 * bc)]) ∧ LiveFrame M0 M L [(bp, bp + 8 * bc)]

theorem FQ.write {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M : Memory}
    (h : FQ R L sp bp bc M0 M) (hLs : LiveSep L [(sp - 4288, sp + 1040)]) {a k : Nat} (v : Nat)
    (hw : (sp - 4288 ≤ a ∧ a + k ≤ sp - 8) ∨ (sp + 8 ≤ a ∧ a + k ≤ sp + 120) ∨ (sp + 224 ≤ a ∧ a + k ≤ sp + 232) ∨
      (sp + 248 ≤ a ∧ a + k ≤ sp + 256) ∨ (sp + 312 ≤ a ∧ a + k ≤ sp + 320) ∨ (sp + 432 ≤ a ∧ a + k ≤ sp + 480) ∨
      (sp + 824 ≤ a ∧ a + k ≤ sp + 832)) :
    FQ R L sp bp bc M0 (M.writeLE a k v) := by
  refine ⟨h.1.writeLE_inRanges v ?_, h.2.writeLE v (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))⟩
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4288, sp - 8), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 8, sp + 120), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 224, sp + 232), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 248, sp + 256), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 312, sp + 320), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 432, sp + 480), by simp [qw], h1, h2⟩
  · exact ⟨(sp + 824, sp + 832), by simp [qw], h1, h2⟩

theorem FQ.call {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M M' : Memory} {rp rc : Nat}
    (h : FQ R L sp bp bc M0 M)
    (hc : MemFrame M M' (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(rp, rp + 8 * rc)]))
    (hl : LiveFrame M M' L [(rp, rp + 8 * rc)]) (hr : bp ≤ rp ∧ rp + 8 * rc ≤ bp + 8 * bc) :
    FQ R L sp bp bc M0 M' := by
  refine ⟨h.1.trans hc (fun a n ho => ⟨ho, ?_⟩),
    h.2.trans (FvModexp.Expmc.liveFrame_widen hl (fun a n ho => ?_)) (fun _ _ h => h)⟩
  · simp only [qw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega

/-- `Env` survives a frame that keeps the guard word -/
theorem env_frame {R : RtInv} {L : List (Nat × Nat)} {g sp : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Env R L g sp M) (hf : MemFrame M M' (R.rt ++ ws)) (hg : Outside (g + 16) 8 ws) : Env R L g sp M' := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs⟩ := h
  have hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨hgrt, hg⟩)
  exact ⟨hal, hsp1, hsp2, by rw [hf.accessible]; exact hacc, hg1, by rw [hf.accessible]; exact hg2,
    by rw [hgr]; exact hg3, hrt, hga, hgrt, hLs⟩

theorem inp_frame {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Inp R L sp n M p) (hf : MemFrame M M' ws) : Inp R L sp n M' p :=
  ⟨by rw [hf.accessible]; exact h.1, h.2⟩

/-- a frame word above the callee window and outside the result buffer reads through a montgomery call -/
theorem rd_call {R : RtInv} {sp a rp rc : Nat} {M M' : Memory}
    (F : MemFrame M M' (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(rp, rp + 8 * rc)]))
    (hwrt : Outside (sp - 4288) (4288 + 1040) R.rt) (hs : 4288 ≤ sp) (h1 : sp + 120 ≤ a) (h2 : a + 8 ≤ sp + 1040)
    (h3 : a + 8 ≤ rp ∨ rp + 8 * rc ≤ a) : M'.readLE a 8 = M.readLE a 8 := by
  refine F.readLE _ _ ?_
  have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
  simp only [outside_append, outside_cons, outside_nil, and_true, hro, true_and]
  omega

theorem OneIn.disj {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M : Memory} (h : OneIn R L sp n M p) :
    (p = sp + 336 ∧ n ≤ 4) ∨ (p + 8 * n ≤ sp - 4288 ∨ sp + 1040 ≤ p) := by
  rcases h with ⟨-, -, -, h⟩ | h
  · right; unfold Apart at h; omega
  · left; exact h

theorem rd_self8 {m : Memory} {a v : Nat} : (m.writeLE a 8 v).readLE a 8 = v % 18446744073709551616 := by
  rw [Memory.readLE_writeLE_self]

set_option maxHeartbeats 0 in
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
