import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmMul
import FvModexp.Proofs.Common.AsmTac
import FvModexp.Proofs.Lib.MulAddVWWAmd64

/-!
# `math/big.mulAddVWW(z, x []Word, m, a Word) (c Word)` (go-bigmodexpfix arith_amd64.s, Go assembly ABI0, amd64): summary

```
z[0:n] = x[0:n] * m + a   (n = len(z)),   c = the carry word out of limb n-1       (len(x) >= len(z))
```

**Summary** (`mulAddVWW_summary`, every `n = len(z)`): from any state at the entry of `mulAddVWW.abi0` whose frame
words describe slices with `x[0:n]` readable and `z[0:n]` writable, in which `z` is equal to or disjoint from `x`
(all package call sites: natmul.go:144, natdiv.go:693 fresh/disjoint `z`; natconv.go:533 in place `z = x`), and `z[0:n]`
is disjoint from the call frame (return address and the 9 argument/result words), the function returns (`RET` to the
pushed return address) with every register but `RSP` (+8) and `RBP` unspecified, and

* `Σ z_i 2^(64 i) = (X·m + a) mod 2^(64 n)` where `X = Σ x_i 2^(64 i)` (limbs BEFORE the call),
* the result word `c = (X·m + a) / 2^(64 n)`,
* memory changed only in `z[0:n]` and the result word.

A 1x loop for `n mod 4` limbs (`MULQ`, `ADDQ`, `ADCQ $0`), then a 4x unrolled loop (the same limb step, four times).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.MulAddVWWAmd64 (program entry)

namespace FvModexp.Amd64.MulAddVWWSum

abbrev head1 : Nat := entry + 0x29
abbrev head4 : Nat := entry + 0x4f
abbrev fin : Nat := entry + 0xaf

structure Ctx (s : State) (z x n m a : Nat) : Prop where
  hz : s.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  hn : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  hx : s.mem.readLE ((s.regs 4).toNat + 32) 8 = x
  hm : s.mem.readLE ((s.regs 4).toNat + 56) 8 = m
  ha : s.mem.readLE ((s.regs 4).toNat + 64) 8 = a
  hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  fb : (s.regs 4).toNat + 80 ≤ 2 ^ 48
  facc : s.mem.accessible (s.regs 4).toNat 80 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  azf : Apart z (8 * n) (s.regs 4).toNat 80


theorem toNat_ofNat64 (v : Nat) : (BitVec.ofNat 64 v).toNat = v % 2 ^ 64 := BitVec.toNat_ofNat _ _

/-- the memory after the call -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      (lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) *
          s.mem.readLE ((s.regs 4).toNat + 56) 8 + s.mem.readLE ((s.regs 4).toNat + 64) 8) %
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  m.readLE ((s.regs 4).toNat + 72) 8 =
      (lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) *
          s.mem.readLE ((s.regs 4).toNat + 56) 8 + s.mem.readLE ((s.regs 4).toNat + 64) 8) /
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 72, (s.regs 4).toNat + 80)]

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)
    (s.mem.readLE ((s.regs 4).toNat + 16) 8) (s.mem.readLE ((s.regs 4).toNat + 56) 8)
    (s.mem.readLE ((s.regs 4).toNat + 64) 8)

theorem rd_frame {m m' : Memory} {z i x n a : Nat} (hf : MemFrame m m' [(z, z + 8 * i)])
    (hal : z = x ∨ Apart z (8 * n) x (8 * n)) (hin : x + 8 * i ≤ a) (hle : a + 8 ≤ x + 8 * n) (hi : i ≤ n) :
    m'.readLE a 8 = m.readLE a 8 :=
  hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hal; omega)

/-- the invariant step of one limb -/
theorem step1 (m m' : Memory) (z x i mv a c : Nat) (hm : mv < 2 ^ 64) (hc : c < 2 ^ 64)
    (hv : lv m' z i + 2 ^ (64 * i) * c = lv m x i * mv + a) :
    lv (m'.writeLE (z + 8 * i) 8 (nr (m.readLE (x + 8 * i) 8) mv c)) z (i + 1) +
        2 ^ (64 * (i + 1)) * (nc (m.readLE (x + 8 * i) 8) mv c % 2 ^ 64) = lv m x (i + 1) * mv + a := by
  rw [Nat.mod_eq_of_lt (nc_lt _ _ _ (limb_lt _ _) hm), lv_write_succ, lv_succ m x, pow_succ64]
  exact mul_step _ _ _ _ _ _ _ _ _ _ hv (mul1n _ _ _ (limb_lt _ _) hm hc)

/-- the invariant step of a block of four limbs -/
theorem step4 (m m' : Memory) (z x i mv a c : Nat) (hm : mv < 2 ^ 64) (hc : c < 2 ^ 64)
    (hv : lv m' z i + 2 ^ (64 * i) * c = lv m x i * mv + a) :
    let a0 := m.readLE (x + 8 * i) 8; let a1 := m.readLE (x + 8 * i + 8) 8
    let a2 := m.readLE (x + 8 * i + 16) 8; let a3 := m.readLE (x + 8 * i + 24) 8
    let c1 := nc a0 mv c; let c2 := nc a1 mv c1; let c3 := nc a2 mv c2
    lv ((((m'.writeLE (z + 8 * i) 8 (nr a0 mv c)).writeLE (z + 8 * i + 8) 8 (nr a1 mv c1)).writeLE
        (z + 8 * i + 16) 8 (nr a2 mv c2)).writeLE (z + 8 * i + 24) 8 (nr a3 mv c3)) z (i + 4) +
        2 ^ (64 * (i + 4)) * (nc a3 mv c3 % 2 ^ 64) = lv m x (i + 4) * mv + a := by
  intro a0 a1 a2 a3 c1 c2 c3
  rw [Nat.mod_eq_of_lt (nc_lt _ _ _ (limb_lt _ _) hm), lv_write4, lv_add4 m x, pow_i4]
  exact mul_step _ _ _ _ _ _ _ _ _ _ hv
    (mulblk4 a0 a1 a2 a3 mv c (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) hm hc c1 c2 c3 rfl rfl rfl)

theorem fin_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) (S : State)
    (hpc : S.rip = BitVec.ofNat 64 fin)
    (hv : lv S.mem z n + 2 ^ (64 * n) * (S.regs 6).toNat = lv s.mem x n * m + a)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)]) (hs : Same64 s S) :
    ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hm, ha, hr, hfb, hfacc, accz, accx, alx, azf⟩ := hc
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs
  unfold Apart at azf
  have hra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  janus64_run [Q]
  have hZ := lv_lt S.mem z n
  have hP : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have e : lv (S.mem.writeLE ((s.regs 4).toNat + 72) 8 (S.regs 6).toNat) z n = lv S.mem z n := by
    unfold lv; exact Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  rw [e]
  refine ⟨hfs, hfw, h87, ?_, ?_, ?_⟩
  · rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hZ]
  · rw [← hv, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hZ]; simp only [Nat.zero_add]
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _
      (r := ((s.regs 4).toNat + 72, (s.regs 4).toNat + 80)) (by simp) (Nat.le_refl _) (by omega)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1

theorem blk_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) :
    ∀ k (S : State) (i : Nat), i + 4 * (k + 1) = n →
      S.rip = BitVec.ofNat 64 head4 → S.regs 7 = BitVec.ofNat 64 (k + 1) → S.regs 3 = BitVec.ofNat 64 m →
      S.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S.regs 9 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * (S.regs 6).toNat = lv s.mem x i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same64 s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hm, ha, hr, hfb, hfacc, accz, accx, alx, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hm64 : m < 2 ^ 64 := hm ▸ limb_lt _ _
  intro k
  induction k with
  | zero =>
    intro S i hi hpc h7 h3 h8 h9 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have hn4 : n = i + 4 := by omega
    subst hn4
    have alx' := alx
    unfold Apart at alx'
    janus64_run until [fin]
    refine fin_lem s hc _ rfl ?_ (frame_ext4 hf _ _ _ _) ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, toNat_ofNat64]
      exact step4 s.mem S.mem z x i m a _ hm64 (S.regs 6).isLt hv
    · same64_tac hs
  | succ k ih =>
    intro S i hi hpc h7 h3 h8 h9 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have alx' := alx
    unfold Apart at alx'
    janus64_run until [head4]
    try simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, rx0, rx1, rx2, rx3]
    refine ih _ (i + 4) (by omega) rfl ?_ ?_ ?_ ?_ ?_ (frame_ext4 hf _ _ _ _) ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, toNat_ofNat64]
      exact step4 s.mem S.mem z x i m a _ hm64 (S.regs 6).isLt hv
    · same64_tac hs

theorem one_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) :
    ∀ j (S : State) (i : Nat), i + (j + 1) = n % 4 →
      S.rip = BitVec.ofNat 64 head1 → S.regs 10 = BitVec.ofNat 64 (j + 1) → S.regs 7 = BitVec.ofNat 64 (n / 4) →
      S.regs 3 = BitVec.ofNat 64 m →
      S.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S.regs 9 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * (S.regs 6).toNat = lv s.mem x i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same64 s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hm, ha, hr, hfb, hfacc, accz, accx, alx, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hm64 : m < 2 ^ 64 := hm ▸ limb_lt _ _
  intro j
  induction j with
  | zero =>
    intro S i hi hpc h10 h7 h3 h8 h9 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    rcases Nat.eq_zero_or_pos (n / 4) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus64_run until [fin]
      try simp only [rx0]
      refine fin_lem s hc _ rfl ?_ (frame_ext hf _) ?_
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, toNat_ofNat64]
        exact step1 s.mem S.mem z x i m a _ hm64 (S.regs 6).isLt hv
      · same64_tac hs
    · obtain ⟨q, hq'⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
      janus64_run until [head4]
      try simp only [rx0]
      refine blk_lem s hc q _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ (frame_ext hf _) ?_
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [h7, hq']
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3
      all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, toNat_ofNat64]
        exact step1 s.mem S.mem z x i m a _ hm64 (S.regs 6).isLt hv
      · same64_tac hs
  | succ j ih =>
    intro S i hi hpc h10 h7 h3 h8 h9 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    janus64_run until [head1]
    try simp only [rx0]
    refine ih _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ (frame_ext hf _) ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h7
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, toNat_ofNat64]
      exact step1 s.mem S.mem z x i m a _ hm64 (S.regs 6).isLt hv
    · same64_tac hs

theorem main_lem {z x n m a : Nat} (s : State) (hc : Ctx s z x n m a) (hpc : s.rip = BitVec.ofNat 64 entry) :
    ReachesRet program (retAddrOf s) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg7, hr, hfb, hfacc, accz, accx, alx, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have hm64 : m < 2 ^ 64 := h_rd_arg6 ▸ limb_lt _ _
  have ha64 : a < 2 ^ 64 := h_rd_arg7 ▸ limb_lt _ _
  have hn64 : n < 2 ^ 64 := by omega
  have hs0 : Same64 s s := Same64.refl s
  have hz0 : lv s.mem z 0 + 2 ^ (64 * 0) * a = lv s.mem x 0 * m + a := by simp [lv_zero]
  have hsh : (BitVec.ofNat 64 n >>> 2).toNat = n / 4 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.shiftRight_eq_div_pow]
  janus64_run until [head1, head4, fin]
  · rw [hsh] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    refine fin_lem s hc _ rfl ?_ (MemFrame.refl _ _) ?_
    · simp [setRegF_apply, lv_zero, toNat_ofNat64, Nat.mod_eq_of_lt ha64]
    · same64_tac hs0
  · rw [hsh] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
    refine blk_lem s hc q _ 0 (by omega) rfl ?r7 ?r3 ?r8 ?r9 ?hv (MemFrame.refl _ _) ?hs
    case r7 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; rw [hsh, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hv => simp [setRegF_apply, lv_zero, toNat_ofNat64, Nat.mod_eq_of_lt ha64]
    case hs => same64_tac hs0
    all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero]
  · obtain ⟨j, hj⟩ : ∃ j, n % 4 = j + 1 := ⟨n % 4 - 1, by omega⟩
    refine one_lem s hc j _ 0 (by omega) rfl ?r10 ?r7 ?r3 ?r8 ?r9 ?hv (MemFrame.refl _ _) ?hs
    case r10 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case r7 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; rw [hsh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hv => simp [setRegF_apply, lv_zero, toNat_ofNat64, Nat.mod_eq_of_lt ha64]
    case hs => same64_tac hs0
    all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero]

/-- `mulAddVWW.abi0` as a callee (library summary: transfers to any program containing these bytes at this address). -/
theorem mulAddVWW_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`z, x` slice bases, `zl` the length of `z`, multiplier `m`, addend `a`) -/
theorem ensures (z zl zc x xl xc m a : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, m, a] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 80)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat =
          (lv s.mem x.toNat zl.toNat * m.toNat + a.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 8 1 =
          [BitVec.ofNat 64 ((lv s.mem x.toNat zl.toNat * m.toNat + a.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 72, (s.regs 4).toNat + 80)]) := by
  refine Ensures0.of_summary0 mulAddVWW_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, alx, azr⟩
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a7 := hs.arg (i := 7) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6 a7
    have hfa := hs.frame_accessible
    have hfb := hs.frame_bound
    simp only [List.length_cons, List.length_nil, Janus.Amd64.GoABI.regSP, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc] at hfa hfb
    have hr := hs.ret
    simp only [Amd64.Program.withExit, Janus.Amd64.GoABI.regSP] at hr
    unfold Pre
    rw [a0, a3, a6, a7, a1]
    exact ⟨a0, a1, a3, a6, a7, by rw [hr]; exact hret.user, by omega, hfa, hz1, hx1, alx, azr⟩
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a7 := hs.arg (i := 7) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6 a7
    unfold Q at hq
    rw [a0, a3, a6, a7, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, Janus.Amd64.GoABI.regSP, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [q2]

end FvModexp.Amd64.MulAddVWWSum
