import FvModexp.Proofs.Arm64.Exp.W4Defs

/-!
# window-4 prologue (arm64): the table loop `powers[i] = buf[i·n:(i+1)·n:(i+2)·n].montgomery(powers[i-1], powers[1], …)`
(nat.go:1415-1417) — shared definitions

The 16 table entries live in one stack nat `buf = (bp, ·, bc)` (`stk.nat(17·n)`), entry `d` at `bp + 8·(d·n)` with
length `n` and capacity `2n`; their slice headers are the frame words `sp + 432 + 24·d` (`var powers [16]nat`).
Continuation form over an anchor memory `M0` (the memory at the first arrival at the loop head, `i = 2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the loop head `CMP $16, R0` (`R0 = i`) -/
abbrev powHead : Nat := 1800300
/-- the loop exit (after the table): `z = z.make(2 * numWords)` -/
abbrev j4 : Nat := 1800364

theorem fnBase' : segAddr LibExp.program W4Loop.fn = 1798512 := by decide

/-- the frame words the table loop writes (callee window, `i+1` at `328`, `24·i` at `320`, headers, `&powers[i]` at `880`) -/
@[reducible] def pw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4288, sp - 8), (sp + 8, sp + 120), (sp + 320, sp + 336), (sp + 432, sp + 816), (sp + 880, sp + 888)]

/-- everything the table loop may change since the anchor -/
@[reducible] def pl (R : RtInv) (sp bp bc : Nat) : List (Nat × Nat) := R.rt ++ pw sp ++ [(bp, bp + 8 * bc)]

@[reducible] def FP (R : RtInv) (L : List (Nat × Nat)) (sp bp bc : Nat) (M0 M : Memory) : Prop :=
  MemFrame M0 M (pl R sp bp bc) ∧ LiveFrame M0 M L [(bp, bp + 8 * bc)]

/-- the static facts of the table loop at the anchor `M0` -/
def PStatic (R : RtInv) (L : List (Nat × Nat)) (g sp n mp mc k0 bp bc : Nat) (M0 : Memory) : Prop :=
  Env R L g sp M0 ∧ 0 < n ∧ n ≤ 2 ^ 16 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧ k0 < 2 ^ 64 ∧ Inp R L sp n M0 mp ∧
  17 * n ≤ bc ∧ bc < 2 ^ 40 ∧ M0.accessible bp (8 * bc) true = true ∧ bp + 8 * bc ≤ 2 ^ 48 ∧
  (InRanges bp (8 * bc) L ∨ Outside bp (8 * bc) R.rt) ∧ Apart bp (8 * bc) (sp - 4288) (4288 + 1040) ∧
  Apart (g + 16) 8 bp (8 * bc) ∧ Apart bp (8 * bc) mp (8 * n) ∧
  M0.readLE (sp + 1016) 8 = mp ∧ M0.readLE (sp + 1024) 8 = n ∧ M0.readLE (sp + 1032) 8 = mc ∧
  M0.readLE (sp + 224) 8 = k0 ∧ M0.readLE (sp + 128) 8 = 2 * n ∧ M0.readLE (sp + 248) 8 = bc ∧
  M0.readLE (sp + 824) 8 = bp ∧
  (∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])

/-- table entry `d` at a loop state: value and header -/
@[reducible] def Ent (sp n bp : Nat) (tbl : Nat → Nat) (M : Memory) (d : Nat) : Prop :=
  M.readLE (bp + 8 * (d * n)) (8 * n) = tbl d ∧ M.readLE (sp + 432 + 24 * d) 8 = bp + 8 * (d * n) ∧
  M.readLE (sp + 440 + 24 * d) 8 = n ∧ M.readLE (sp + 448 + 24 * d) 8 = 2 * n

theorem FP.write {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M : Memory}
    (h : FP R L sp bp bc M0 M) (hLs : LiveSep L [(sp - 4288, sp + 1040)]) {a k : Nat} (v : Nat)
    (hw : (sp - 4288 ≤ a ∧ a + k ≤ sp - 8) ∨ (sp + 8 ≤ a ∧ a + k ≤ sp + 120) ∨ (sp + 320 ≤ a ∧ a + k ≤ sp + 336) ∨
      (sp + 432 ≤ a ∧ a + k ≤ sp + 816) ∨ (sp + 880 ≤ a ∧ a + k ≤ sp + 888)) :
    FP R L sp bp bc M0 (M.writeLE a k v) := by
  refine ⟨h.1.writeLE_inRanges v ?_, h.2.writeLE v (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))⟩
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4288, sp - 8), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 8, sp + 120), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 320, sp + 336), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 432, sp + 816), by simp [pl, pw], h1, h2⟩
  · exact ⟨(sp + 880, sp + 888), by simp [pl, pw], h1, h2⟩

theorem FP.call {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M M' : Memory} {rp rc : Nat}
    (h : FP R L sp bp bc M0 M)
    (hc : MemFrame M M' (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(rp, rp + 8 * rc)]))
    (hl : LiveFrame M M' L [(rp, rp + 8 * rc)]) (hr : bp ≤ rp ∧ rp + 8 * rc ≤ bp + 8 * bc) :
    FP R L sp bp bc M0 M' := by
  refine ⟨h.1.trans hc (fun a n ho => ⟨ho, ?_⟩),
    h.2.trans (FvModexp.Expmc.liveFrame_widen hl (fun a n ho => ?_)) (fun _ _ h => h)⟩
  · simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega

theorem rd_w8 {m : Memory} {a b v : Nat} (h : a = b) (hv : v < 2 ^ 64) : (m.writeLE a 8 v).readLE b 8 = v := by
  subst h; rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at hv ⊢; exact hv)

/-- the executor's `MUL`s of the loop head (`n · (i + c)`, `n · i`) -/
theorem mulw (n i c : Nat) (hn : n ≤ 2 ^ 16) (hi : i < 16) (hc : c ≤ 2) :
    BitVec.ofNat 64 n * (BitVec.ofNat 64 i + BitVec.ofNat 64 c) = BitVec.ofNat 64 (i * n + c * n) := by
  have e : n * (i + c) = i * n + c * n := by rw [Nat.mul_comm, Nat.add_mul]
  have h1 : i * n + c * n < 2 ^ 64 := by
    have := Nat.mul_le_mul (show i ≤ 16 by omega) hn; have := Nat.mul_le_mul hc hn; omega
  have h2 : n * (i + c) < 2 ^ 64 := e ▸ h1
  apply BitVec.eq_of_toNat_eq
  simp (disch := omega) only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact e

theorem mulw0 (n i : Nat) (hn : n ≤ 2 ^ 16) (hi : i < 16) :
    BitVec.ofNat 64 n * BitVec.ofNat 64 i = BitVec.ofNat 64 (i * n) := by
  have h1 : i * n < 2 ^ 64 := by have := Nat.mul_le_mul (show i ≤ 16 by omega) hn; omega
  have h2 : n * i < 2 ^ 64 := Nat.mul_comm i n ▸ h1
  apply BitVec.eq_of_toNat_eq
  simp (disch := omega) only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.mul_comm n i

/-- a table slice `buf[d·n : … : (d+2)·n]` (`d ≤ 15`) is a montgomery result buffer -/
theorem buf_sub {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g sp n mp mc k0 bp bc M0) {d : Nat} (hd : d ≤ 15) :
    Buf R L g sp n M0 (bp + 8 * (d * n)) (2 * n) := by
  obtain ⟨-, hn, hn16, -, -, -, -, hbc, hbc', hba, hbb, hbh, hbw, hbg, -⟩ := hs
  have e1 : d * n + 2 * n ≤ bc := by
    have := Nat.mul_le_mul_right n (show d + 2 ≤ 17 by omega); rw [Nat.add_mul] at this; omega
  refine ⟨Nat.le_refl _, by omega, M0.accessible_sub hba (Or.inr rfl) (by omega) (by omega), by omega,
    hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_, ?_⟩
  · unfold Apart at hbw ⊢; omega
  · unfold Apart at hbg ⊢; omega

/-- a table entry is a montgomery input -/
theorem inp_ent {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g sp n mp mc k0 bp bc M0) {d : Nat} (hd : d ≤ 16) :
    Inp R L sp n M0 (bp + 8 * (d * n)) := by
  obtain ⟨-, hn, hn16, -, -, -, -, hbc, hbc', hba, hbb, hbh, hbw, hbg, -⟩ := hs
  have e1 : d * n + n ≤ bc := by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ 17 by omega); rw [Nat.add_mul] at this; omega
  refine ⟨M0.accessible_sub hba (Or.inr rfl) (by omega) (by omega), by omega,
    hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_⟩
  unfold Apart at hbw ⊢; omega

/-- the entries `d < i` survive one table step (the call writes `buf[i·n:(i+2)·n]`, then the header of entry `i`) -/
theorem ents_step {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g sp n mp mc k0 bp bc M0) {tbl : Nat → Nat} {i : Nat} (hi2 : 2 ≤ i) (hi : i < 16)
    {M M1 : Memory} {v0 : Nat} (hE : ∀ d, d < i → Ent sp n bp tbl M d)
    (F1 : MemFrame (((M.writeLE (sp + 328) 8 (i + 1)).writeLE (sp + 320) 8 (8 * i + 2 * (8 * i))).writeLE (sp + 880) 8
      (sp + 432 + (8 * i + 2 * (8 * i)))) M1
      (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(bp + 8 * (i * n), bp + 8 * (i * n) + 8 * (2 * n))]))
    (L1 : LiveFrame (((M.writeLE (sp + 328) 8 (i + 1)).writeLE (sp + 320) 8 (8 * i + 2 * (8 * i))).writeLE (sp + 880) 8
      (sp + 432 + (8 * i + 2 * (8 * i)))) M1 L [(bp + 8 * (i * n), bp + 8 * (i * n) + 8 * (2 * n))]) :
    ∀ d, d < i → Ent sp n bp tbl (((M1.writeLE (sp + (432 + (8 * i + 2 * (8 * i)))) 8 v0).writeLE
      (sp + 432 + (8 * i + 2 * (8 * i)) + 8) 8 n).writeLE (sp + 432 + (8 * i + 2 * (8 * i)) + 16) 8 (2 * n)) d := by
  have hs0 := hs
  obtain ⟨⟨-, hsp1, -, -, -, -, -, hwrt, -, -, -⟩, hn, hn16, -, -, -, -, hbc, -, -, hbb, -, hbw, -⟩ := hs0
  intro d hd
  obtain ⟨q0, q1, q2, q3⟩ := hE d hd
  have hh := (inp_ent hs (d := d) (by omega)).2.2.1
  have h1 : d * n + n ≤ i * n := by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ i by omega); rw [Nat.succ_mul] at this; exact this
  have h2 : i * n + 2 * n ≤ 17 * n := by
    have := Nat.mul_le_mul_right n (show i + 2 ≤ 17 by omega); rw [Nat.add_mul] at this; omega
  unfold Apart at hbw
  have thru : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 1040 →
      M1.readLE a 8 = (((M.writeLE (sp + 328) 8 (i + 1)).writeLE (sp + 320) 8 (8 * i + 2 * (8 * i))).writeLE
        (sp + 880) 8 (sp + 432 + (8 * i + 2 * (8 * i)))).readLE a 8 := by
    intro a ha1 ha2
    refine F1.readLE _ _ ?_
    have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
    simp only [outside_append, outside_cons, outside_nil, and_true, hro, true_and]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [FvModexp.Expmc.held_readLE hh F1 L1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact q0
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [thru _ (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact q1
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [thru _ (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact q2
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [thru _ (by omega) (by omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact q3

/-- entry `i` after its table step -/
theorem ent_new {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g sp n mp mc k0 bp bc M0) {tbl : Nat → Nat} {i : Nat} (hi2 : 2 ≤ i) (hi : i < 16)
    {M M1 : Memory} (hE : ∀ d, d < i → Ent sp n bp tbl M d) (hF : FP R L sp bp bc M0 M)
    (v1 : M1.readLE (bp + 8 * (i * n)) (8 * n) =
      Exp.montgomery n (M.readLE (bp + 8 * ((i - 1) * n)) (8 * n)) (M.readLE (bp + 8 * n) (8 * n))
        ((((M.writeLE (sp + 328) 8 (i + 1)).writeLE (sp + 320) 8 (8 * i + 2 * (8 * i))).writeLE (sp + 880) 8
          (sp + 432 + (8 * i + 2 * (8 * i)))).readLE mp (8 * n)) k0) :
    Ent sp n bp (fun _ => Exp.montgomery n (tbl (i - 1)) (tbl 1) (M0.readLE mp (8 * n)) k0)
      (((M1.writeLE (sp + (432 + (8 * i + 2 * (8 * i)))) 8 (bp + 8 * (i * n))).writeLE
        (sp + 432 + (8 * i + 2 * (8 * i)) + 8) 8 n).writeLE (sp + 432 + (8 * i + 2 * (8 * i)) + 16) 8 (2 * n)) i := by
  have hs0 := hs
  obtain ⟨⟨-, hsp1, -, -, -, -, -, hwrt, -, -, -⟩, hn, hn16, -, -, -, hm, hbc, -, -, hbb, -, hbw, -, hbm, -⟩ := hs0
  obtain ⟨q0, -, -, -⟩ := hE (i - 1) (by omega)
  obtain ⟨p0, -, -, -⟩ := hE 1 (by omega)
  rw [Nat.one_mul] at p0
  have h2 : i * n + 2 * n ≤ 17 * n := by
    have := Nat.mul_le_mul_right n (show i + 2 ≤ 17 by omega); rw [Nat.add_mul] at this; omega
  have u3 := hm.2.2.2
  unfold Apart at hbw u3
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [v1, q0, p0]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [FvModexp.Expmc.held_readLE hm.2.2.1 hF.1 hF.2 (by simp only [pw, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hbm; simp only [outside_cons, outside_nil, and_true]; omega)]
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact rd_w8 (by omega) (by omega)
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact rd_w8 (by omega) (by omega)
  · exact rd_w8 (by omega) (by omega)

end FvModexp.Arm64.W4Pro
