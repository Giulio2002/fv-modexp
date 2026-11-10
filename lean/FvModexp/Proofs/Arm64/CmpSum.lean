import FvModexp.Proofs.Common.AsmCmp
import FvModexp.Proofs.Lib.CmpA64

/-!
# `math/big.nat.cmp(x, y nat) (r int)` (go-bigmodexpfix nat.go:152-180, Go ABIInternal, arm64): summary

```go
func (x nat) cmp(y nat) (r int) {
	m := len(x); n := len(y)
	if m != n || m == 0 { switch { case m < n: r = -1; case m > n: r = 1 }; return }
	i := m - 1
	for i > 0 && x[i] == y[i] { i-- }
	switch { case x[i] < y[i]: r = -1; case x[i] > y[i]: r = 1 }
	return
}
```

**Summary** (`cmp_summary`): from any state at the entry with `x = (X0, X1, X2)`, `y = (X3, X4, X5)` (pointer, length,
capacity), the stack guard passing (`GuardOK s 0`), the 24 bytes below `SP` and the 40 above writable (`StackOK s 24 40`:
frame record and the two argument spill slots), and each slice either empty or readable and outside that stack
window, the function returns to `X30` with `X0 = cmpRes m n X Y` (`-1`/`0`/`1` as a 64-bit word: lengths first, then,
for equal lengths, the values `X = Σ x_i 2^(64 i)`, `Y = Σ y_i 2^(64 i)`), only `X1 X2 X4 X5 X16`, the flags and the
memory of its frame record and the two spill slots changed. (`nat.cmp` compares lengths first: it is the comparison of
values only for normalized nats, which is the callers' business.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.CmpA64 (program entry)

namespace FvModexp.Arm64.CmpSum

abbrev head : Nat := entry + 0x60

/-- the result of `nat.cmp` as the 64-bit word in `X0` -/
def cmpRes (m n X Y : Nat) : BitVec 64 :=
  if m < n then 18446744073709551615#64 else if n < m then 1#64
  else if X < Y then 18446744073709551615#64 else if Y < X then 1#64 else 0#64

/-- the stack window written: frame record `[SP-24, SP-8)`, spill slots of `x.ptr` and `y.ptr` -/
def frame (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat + 32, s.sp.toNat + 40)]

/-- a slice argument that the function may read: empty, or readable and outside the stack window -/
def SliceOK (s : State) (p n : Nat) : Prop :=
  n = 0 ∨ (s.mem.accessible p (8 * n) false = true ∧ Apart p (8 * n) (s.sp.toNat - 24) 64)

def Pre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0 ∧ StackOK s 24 40 ∧
  SliceOK s (s.regs 0).toNat (s.regs 1).toNat ∧ SliceOK s (s.regs 3).toNat (s.regs 4).toNat

def Post (s s' : State) : Prop :=
  ∃ (v1 v2 v4 v5 v16 : BitVec 64) (f : Flags) (m : Memory),
    s' = { s with regs := setReg (setReg (setReg (setReg (setReg (setReg s.regs 0
              (cmpRes (s.regs 1).toNat (s.regs 4).toNat (lv s.mem (s.regs 0).toNat (s.regs 1).toNat)
                (lv s.mem (s.regs 3).toNat (s.regs 4).toNat))) 1 v1) 2 v2) 4 v4) 5 v5) 16 v16,
                  pc := s.regs 30, flags := f, mem := m } ∧
    MemFrame s.mem m (frame s)

theorem res_lt (m : Memory) (x y k n : Nat) (hk : k < n) (ht : top m x k n = top m y k n)
    (hl : ¬ m.readLE (y + k * 8) 8 ≤ m.readLE (x + k * 8) 8) : cmpRes n n (lv m x n) (lv m y n) = 18446744073709551615#64 := by
  have := lv_lt_of_top m x y k n hk ht (by rw [Nat.mul_comm 8 k]; omega)
  simp [cmpRes, this]

theorem res_gt (m : Memory) (x y k n : Nat) (hk : k < n) (ht : top m x k n = top m y k n)
    (hl : ¬ m.readLE (x + k * 8) 8 ≤ m.readLE (y + k * 8) 8) : cmpRes n n (lv m x n) (lv m y n) = 1#64 := by
  have := lv_lt_of_top m y x k n hk ht.symm (by rw [Nat.mul_comm 8 k]; omega)
  simp [cmpRes, this, Nat.lt_asymm this]

theorem res_eq (m : Memory) (x y n : Nat) (hn : 0 < n) (ht : top m x 0 n = top m y 0 n)
    (h1 : m.readLE y 8 ≤ m.readLE x 8) (h2 : m.readLE x 8 ≤ m.readLE y 8) :
    cmpRes n n (lv m x n) (lv m y n) = 0#64 := by
  have := lv_eq_of_top m x y n hn ht (by omega)
  simp [cmpRes, this]

abbrev exitPc : Nat := entry + 0x78

/-- from the loop exit (`i = k`, limbs above `k` equal, and `k = 0` or limb `k` differs) to the return -/
theorem exit_lem (s : State) (hmn : (s.regs 1).toNat = (s.regs 4).toNat) (hpos : 0 < (s.regs 1).toNat)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hb : 24 ≤ s.sp.toNat) (hbb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 24) (24 + 40) true = true)
    (hax : s.mem.accessible (s.regs 0).toNat (8 * (s.regs 1).toNat) false = true)
    (hay : s.mem.accessible (s.regs 3).toNat (8 * (s.regs 1).toNat) false = true)
    (hxa : Apart (s.regs 0).toNat (8 * (s.regs 1).toNat) (s.sp.toNat - 24) 64)
    (hya : Apart (s.regs 3).toNat (8 * (s.regs 1).toNat) (s.sp.toNat - 24) 64)
    (M : Memory) (hM : MemFrame s.mem M (frame s))
    (h_rd29 : M.readLE (s.sp.toNat - 24) 8 = (s.regs 29).toNat)
    (h_rd30 : M.readLE (s.sp.toNat - 16) 8 = (s.regs 30).toNat) :
    ∀ k (R : Nat → BitVec 64) (P : BitVec 64) (f : Flags) (v4 v5 v16 : BitVec 64), k < (s.regs 1).toNat →
      P = BitVec.ofNat 64 exitPc →
      top s.mem (s.regs 0).toNat k (s.regs 1).toNat = top s.mem (s.regs 3).toNat k (s.regs 1).toNat →
      (k = 0 ∨ s.mem.readLE ((s.regs 0).toNat + k * 8) 8 ≠ s.mem.readLE ((s.regs 3).toNat + k * 8) 8) →
      R = setReg (setReg (setReg (setReg (setReg s.regs 2 (BitVec.ofNat 64 k)) 4 v4) 5 v5) 16 v16) 29 (s.sp - 24#64) →
      ReachesRet program (s.regs 30)
        { s with regs := R, sp := s.sp - 16#64, pc := P, flags := f, mem := M } (Post s) := by
  have bx := Memory.accessible_bound _ hax
  have by' := Memory.accessible_bound _ hay
  intro k R P f v4 v5 v16 hk hP ht hne hR
  subst hR hP
  simp only [exitPc, FvModexp.Lib.CmpA64.entry, Nat.reduceAdd]
  have h_rdx : M.readLE ((s.regs 0).toNat + k * 8) 8 = s.mem.readLE ((s.regs 0).toNat + k * 8) 8 :=
    hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hxa; omega)
  have h_rdy : M.readLE ((s.regs 3).toNat + k * 8) 8 = s.mem.readLE ((s.regs 3).toNat + k * 8) 8 :=
    hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hya; omega)
  janus_run
  all_goals simp only [h_rdx, h_rdy] at *
  all_goals (unfold Post; rw [← hmn])
  · have h1 : s.mem.readLE ((s.regs 3).toNat + k * 8) 8 ≤ s.mem.readLE ((s.regs 0).toNat + k * 8) 8 := by janus_assumption
    have h2 : s.mem.readLE ((s.regs 0).toNat + k * 8) 8 ≤ s.mem.readLE ((s.regs 3).toNat + k * 8) 8 := by janus_assumption
    have hk0 : k = 0 := by rcases hne with h | h; exact h; exact absurd (by omega) h
    subst hk0
    simp only [Nat.zero_mul, Nat.add_zero] at h1 h2
    rw [res_eq s.mem _ _ _ hpos ht h1 h2]
    exact ⟨_, _, _, _, _, _, _, rfl, hM⟩
  · rw [res_gt s.mem (s.regs 0).toNat (s.regs 3).toNat k _ hk ht (by janus_assumption)]
    exact ⟨_, _, _, _, _, _, _, rfl, hM⟩
  · rw [res_lt s.mem (s.regs 0).toNat (s.regs 3).toNat k _ hk ht (by janus_assumption)]
    exact ⟨_, _, _, _, _, _, _, rfl, hM⟩


/-- the loop head `CMP X2, #0` (`i = k`, limbs above `k` equal) -/
theorem loop (s : State) (hmn : (s.regs 1).toNat = (s.regs 4).toNat) (hpos : 0 < (s.regs 1).toNat)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hb : 24 ≤ s.sp.toNat) (hbb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 24) (24 + 40) true = true)
    (hax : s.mem.accessible (s.regs 0).toNat (8 * (s.regs 1).toNat) false = true)
    (hay : s.mem.accessible (s.regs 3).toNat (8 * (s.regs 1).toNat) false = true)
    (hxa : Apart (s.regs 0).toNat (8 * (s.regs 1).toNat) (s.sp.toNat - 24) 64)
    (hya : Apart (s.regs 3).toNat (8 * (s.regs 1).toNat) (s.sp.toNat - 24) 64)
    (M : Memory) (hM : MemFrame s.mem M (frame s))
    (h_rd29 : M.readLE (s.sp.toNat - 24) 8 = (s.regs 29).toNat)
    (h_rd30 : M.readLE (s.sp.toNat - 16) 8 = (s.regs 30).toNat) :
    ∀ k (R : Nat → BitVec 64) (P : BitVec 64) (f : Flags) (v4 v5 v16 : BitVec 64), k < (s.regs 1).toNat →
      P = BitVec.ofNat 64 head →
      top s.mem (s.regs 0).toNat k (s.regs 1).toNat = top s.mem (s.regs 3).toNat k (s.regs 1).toNat →
      R = setReg (setReg (setReg (setReg (setReg s.regs 2 (BitVec.ofNat 64 k)) 4 v4) 5 v5) 16 v16) 29 (s.sp - 24#64) →
      ReachesRet program (s.regs 30)
        { s with regs := R, sp := s.sp - 16#64, pc := P, flags := f, mem := M } (Post s) := by
  have bx := Memory.accessible_bound _ hax
  have by' := Memory.accessible_bound _ hay
  have hex := exit_lem s hmn hpos h30a h30b hal hb hbb hw hax hay hxa hya M hM h_rd29 h_rd30
  intro k
  induction k with
  | zero =>
    intro R P f v4 v5 v16 hk hP ht hR
    subst hR hP
    simp only [head, FvModexp.Lib.CmpA64.entry, Nat.reduceAdd]
    janus_run until [entry + 0x78]
    exact hex 0 _ _ _ _ _ _ hk rfl ht (Or.inl rfl) rfl
  | succ k ih =>
    intro R P f v4 v5 v16 hk hP ht hR
    subst hR hP
    simp only [head, FvModexp.Lib.CmpA64.entry, Nat.reduceAdd]
    have h_rdx : M.readLE ((s.regs 0).toNat + (k + 1) * 8) 8 = s.mem.readLE ((s.regs 0).toNat + (k + 1) * 8) 8 :=
      hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hxa; omega)
    have h_rdy : M.readLE ((s.regs 3).toNat + (k + 1) * 8) 8 = s.mem.readLE ((s.regs 3).toNat + (k + 1) * 8) 8 :=
      hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hya; omega)
    have hsub : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run until [entry + 0x60, entry + 0x78]
    · refine ih _ _ _ _ _ _ (by omega) (by decide) ?_ (by rw [hsub])
      rw [top_step s.mem _ k _ (by omega), top_step s.mem _ k _ (by omega), ht]
      rw [Nat.mul_comm 8 (k + 1), hbr]
    · exact hex (k + 1) _ _ _ _ _ _ hk (by decide) ht (Or.inr fun h => hbr h.symm) rfl

theorem regs_init (r : Nat → BitVec 64) (a b c : BitVec 64) :
    setReg (setReg (setReg r 2 a) 16 b) 29 c = setReg (setReg (setReg (setReg (setReg r 2 a) 4 (r 4)) 5 (r 5)) 16 b) 29 c := by
  funext j
  simp only [setReg]
  by_cases h4 : j = 4
  · subst h4; simp
  · by_cases h5 : j = 5
    · subst h5; simp
    · simp [h4, h5]

/-- `Post` for an early return (only `X0` and the guard scratch `X16` written) -/
theorem post_intro (s : State) (R g : BitVec 64) (f : Flags) (m : Memory)
    (hR : R = cmpRes (s.regs 1).toNat (s.regs 4).toNat (lv s.mem (s.regs 0).toNat (s.regs 1).toNat)
      (lv s.mem (s.regs 3).toNat (s.regs 4).toNat))
    (hm : MemFrame s.mem m (frame s)) :
    Post s { s with regs := setReg (setReg s.regs 0 R) 16 g, pc := s.regs 30, flags := f, mem := m } := by
  refine ⟨s.regs 1, s.regs 2, s.regs 4, s.regs 5, g, f, m, ?_, hm⟩
  subst hR
  congr 1
  funext j
  simp only [setReg]
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h16 : j = 16
    · simp [h16]
    · by_cases h1 : j = 1
      · subst h1; simp
      · by_cases h2 : j = 2
        · subst h2; simp
        · by_cases h4 : j = 4
          · subst h4; simp
          · by_cases h5 : j = 5
            · subst h5; simp
            · simp [h0, h16, h1, h2, h4, h5]

theorem cmp_summary : Summary program entry Pre Post := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, hbb, hw⟩, hsx, hsy⟩
  have hmb : (s.regs 1).toNat ≤ 2 ^ 45 := by
    rcases hsx with h | ⟨h, _⟩
    · omega
    · have := Memory.accessible_bound _ h; omega
  have hnb : (s.regs 4).toNat ≤ 2 ^ 45 := by
    rcases hsy with h | ⟨h, _⟩
    · omega
    · have := Memory.accessible_bound _ h; omega
  rcases Nat.eq_zero_or_pos (s.regs 1).toNat with hm0 | hpos
  · rcases Nat.eq_zero_or_pos (s.regs 4).toNat with hn0 | hnpos
    all_goals janus_run until [head]
    all_goals
      refine post_intro s _ _ _ _ ?_ (by unfold frame; janus_frame)
      simp only [cmpRes, hm0, lv_zero]
      try simp only [hn0, lv_zero]
      repeat' split
      all_goals first | rfl | (exfalso; omega)
  janus_run until [head]
  rotate_left
  all_goals try (
      refine post_intro s _ _ _ _ ?_ (by unfold frame; janus_frame)
      simp only [cmpRes]
      repeat' split
      all_goals first | rfl | (exfalso; omega))
  · have hmn : (s.regs 1).toNat = (s.regs 4).toNat := by janus_assumption
    obtain ⟨hax, hxa⟩ := hsx.resolve_left (by omega)
    obtain ⟨hay, hya⟩ := hsy.resolve_left (by omega)
    rw [← hmn] at hay hya
    have hsub : s.regs 1 - 1#64 = BitVec.ofNat 64 ((s.regs 1).toNat - 1) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine loop s hmn hpos h30a h30b hal hb hbb hw hax hay hxa hya _ (by unfold frame; janus_frame) ?_ ?_
      ((s.regs 1).toNat - 1) _ _ _ _ _ _ (by omega) (by decide)
      (by rw [top_last _ _ _ hpos, top_last _ _ _ hpos]) (by rw [hsub, regs_init])
    · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 29).isLt
    · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 30).isLt

end FvModexp.Arm64.CmpSum
