import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Lib.SubVVA64

/-!
# `math/big.subVV(z, x, y []Word) (c Word)` (go-bigmodexpfix arith_arm64.s:53-99, Go assembly ABI0, arm64): summary

```
z[i] = (x[i] - y[i] - borrow) mod 2^64 for i < len(z), c = final borrow          (len(x), len(y) >= len(z))
```

**Summary** (`subVV_summary`, for every length `n = len(z)`): from any state at the entry of `subVV.abi0` whose frame
words describe slices with `x[0:n]`, `y[0:n]` readable and `z[0:n]` writable, in which `z` is equal to or disjoint from
`x` and from `y`, and `z` is disjoint from the result word, the function returns with every register but `R18`, `g`,
`FP`, `SP` unspecified and, for `X = Σ x_i 2^(64 i)`, `Y = Σ y_i 2^(64 i)` (limbs BEFORE the call),

* `Σ z_i 2^(64 i) + Y = X + 2^(64 n) · c` (so `Σ z_i 2^(64 i) = (X + 2^(64 n) - Y) mod 2^(64 n)`),
* the result word `c = 1` if `X < Y`, else `0` (the borrow),
* memory changed only in `z[0:n]` and the result word.

`SBCS` computes `a + NOT b + C` (`C` = not borrow); the invariant is `Z_i + Y_i = X_i + 2^(64 i) (1 - C)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.SubVVA64 (program entry)

namespace FvModexp.Arm64.SubVVSum

abbrev head1 : Nat := entry + 0x20
abbrev head4 : Nat := entry + 0x3c
abbrev fin : Nat := entry + 0x6c

/-- the preconditions at the entry (frame words: `z, len, cap, x, len, cap, y, len, cap, c`) -/
structure Ctx (s : State) (z x y n : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hy : s.mem.readLE (s.sp.toNat + 56) 8 = y
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 88 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 80 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 80) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 56) 8)
    (s.mem.readLE (s.sp.toNat + 16) 8)

/-- the memory after the call -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
      lv s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
    lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
      2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) * m.readLE (s.sp.toNat + 80) 8 ∧
  m.readLE (s.sp.toNat + 80) 8 =
    (if lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) <
        lv s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8) then 1 else 0) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 80, s.sp.toNat + 88)]

/-- one `SBCS` limb: `r + b + (1 - C) = a + 2^64 (1 - C')` -/
theorem sbc_val (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (c : Bool) :
    (addWithCarry (BitVec.ofNat 64 a) (~~~BitVec.ofNat 64 b) c).fst.toNat + b + (1 - c.toNat) =
      a + 2 ^ 64 * (1 - (addWithCarry (BitVec.ofNat 64 a) (~~~BitVec.ofNat 64 b) c).snd.c.toNat) := by
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  simp only [addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : 2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c.toNat
  · have e : (a + (2 ^ 64 - 1 - b) + c.toNat) % 2 ^ 64 ≠ a + (2 ^ 64 - 1 - b) + c.toNat := by omega
    simp only [ne_eq, e, not_false_eq_true, decide_true, Bool.toNat_true]; omega
  · have e : (a + (2 ^ 64 - 1 - b) + c.toNat) % 2 ^ 64 = a + (2 ^ 64 - 1 - b) + c.toNat := Nat.mod_eq_of_lt (by omega)
    simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.toNat_false]; omega

/-- the limb step of a subtraction chain: `Z + B = A + P·bo`, `r + b + bo = a + W·bo'` -/
theorem sub_step (P W Z bo A B a b r bo' : Nat) (hs : Z + B = A + P * bo) (ht : r + b + bo = a + W * bo') :
    (Z + P * r) + (B + P * b) = (A + P * a) + (P * W) * bo' := by
  have h1 : P * (r + b + bo) = P * (a + W * bo') := by rw [ht]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc] at h1
  omega

/-- the invariant step of one limb -/
theorem step1 (m m' : Memory) (z x y i : Nat) (c : Bool)
    (hv : lv m' z i + lv m y i = lv m x i + 2 ^ (64 * i) * (1 - c.toNat)) :
    lv (m'.writeLE (z + 8 * i) 8 (addWithCarry (BitVec.ofNat 64 (m.readLE (x + 8 * i) 8))
        (~~~BitVec.ofNat 64 (m.readLE (y + 8 * i) 8)) c).fst.toNat) z (i + 1) + lv m y (i + 1) =
      lv m x (i + 1) + 2 ^ (64 * (i + 1)) * (1 - (addWithCarry (BitVec.ofNat 64 (m.readLE (x + 8 * i) 8))
        (~~~BitVec.ofNat 64 (m.readLE (y + 8 * i) 8)) c).snd.c.toNat) := by
  rw [lv_write_succ, lv_succ m x, lv_succ m y, pow_succ64, toNat_mod64]
  exact sub_step _ _ _ _ _ _ _ _ _ _ hv (sbc_val _ _ (limb_lt _ _) (limb_lt _ _) c)

/-- `SBCS` result and carry on limbs `a`, `b` -/
abbrev sr (a b : Nat) (c : Bool) : BitVec 64 := (addWithCarry (BitVec.ofNat 64 a) (~~~BitVec.ofNat 64 b) c).fst
abbrev sc (a b : Nat) (c : Bool) : Bool := (addWithCarry (BitVec.ofNat 64 a) (~~~BitVec.ofNat 64 b) c).snd.c

/-- the invariant step of a block of four limbs -/
theorem step4 (m m' : Memory) (z x y i : Nat) (c : Bool)
    (hv : lv m' z i + lv m y i = lv m x i + 2 ^ (64 * i) * (1 - c.toNat)) :
    let a0 := m.readLE (x + 8 * i) 8; let a1 := m.readLE (x + 8 * i + 8) 8
    let a2 := m.readLE (x + 8 * i + 16) 8; let a3 := m.readLE (x + 8 * i + 24) 8
    let b0 := m.readLE (y + 8 * i) 8; let b1 := m.readLE (y + 8 * i + 8) 8
    let b2 := m.readLE (y + 8 * i + 16) 8; let b3 := m.readLE (y + 8 * i + 24) 8
    let c1 := sc a0 b0 c; let c2 := sc a1 b1 c1; let c3 := sc a2 b2 c2
    lv ((((m'.writeLE (z + 8 * i) 8 (sr a0 b0 c).toNat).writeLE (z + 8 * i + 8) 8 (sr a1 b1 c1).toNat).writeLE
        (z + 8 * i + 16) 8 (sr a2 b2 c2).toNat).writeLE (z + 8 * i + 24) 8 (sr a3 b3 c3).toNat) z (i + 4) +
        lv m y (i + 4) =
      lv m x (i + 4) + 2 ^ (64 * (i + 4)) * (1 - (sc a3 b3 c3).toNat) := by
  intro a0 a1 a2 a3 b0 b1 b2 b3 c1 c2 c3
  rw [lv_write4, lv_add4 m x, lv_add4 m y, pow_i4]
  simp only [toNat_mod64]
  have k0 := sbc_val a0 b0 (limb_lt _ _) (limb_lt _ _) c
  have k1 := sbc_val a1 b1 (limb_lt _ _) (limb_lt _ _) c1
  have k2 := sbc_val a2 b2 (limb_lt _ _) (limb_lt _ _) c2
  have k3 := sbc_val a3 b3 (limb_lt _ _) (limb_lt _ _) c3
  have l1 : c1.toNat ≤ 1 := by cases c1 <;> simp
  have l2 : c2.toNat ≤ 1 := by cases c2 <;> simp
  have l3 : c3.toNat ≤ 1 := by cases c3 <;> simp
  have hsum : ((sr a0 b0 c).toNat + 2 ^ 64 * (sr a1 b1 c1).toNat + 2 ^ 128 * (sr a2 b2 c2).toNat +
      2 ^ 192 * (sr a3 b3 c3).toNat) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) + (1 - c.toNat) =
      (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + 2 ^ 256 * (1 - (sc a3 b3 c3).toNat) := by
    simp only [c1, c2, c3, sr, sc] at k0 k1 k2 k3 l1 l2 l3 ⊢
    omega
  exact sub_step _ _ _ _ _ _ _ _ _ _ hv hsum

/-- the equations every loop state shares with the entry state `s` -/
structure Same (s S : State) : Prop where
  sp : S.sp = s.sp
  r18 : S.regs 18 = s.regs 18
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.regs 29
  r30 : S.regs 30 = s.regs 30
  fpcr : S.fpcr = s.fpcr
  tpidr : S.tpidr = s.tpidr
  dczid : S.dczid = s.dczid
  excl : S.excl = s.excl
  exclPass : S.exclPass = s.exclPass

/-- closes `Same s S'` for a state `S'` reached from a `Same s S` state without touching the kept registers -/
macro "same_tac " h:ident : tactic => `(tactic| (
  obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := $h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | rfl | exact hsp
  · janus_simp
  · janus_simp
  · janus_simp
  · janus_simp
  · first | rfl | exact hfp
  · first | rfl | exact htp
  · first | rfl | exact hdc
  · first | rfl | exact hex
  · first | rfl | exact hep))

theorem rd_frame {m m' : Memory} {z i x n a : Nat} (hf : MemFrame m m' [(z, z + 8 * i)])
    (hal : z = x ∨ Apart z (8 * n) x (8 * n)) (hin : x + 8 * i ≤ a) (hle : a + 8 ≤ x + 8 * n) (hi : i ≤ n) :
    m'.readLE a 8 = m.readLE a 8 :=
  hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hal; omega)

/-- `SBC x, x, x; NEG x`: the borrow `1 - C` -/
theorem borrow_nat (r : BitVec 64) (c : Bool) :
    (18446744073709551616 - (r.toNat + (~~~r).toNat + c.toNat) % 18446744073709551616) % 18446744073709551616 =
      1 - c.toNat := by
  have hv := r.isLt
  rw [BitVec.toNat_not]
  cases c <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

theorem fin_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) (S : State) (c : Bool)
    (hpc : S.pc = BitVec.ofNat 64 fin) (hcf : S.flags.c = c)
    (hv : lv S.mem z n + lv s.mem y n = lv s.mem x n + 2 ^ (64 * n) * (1 - c.toNat))
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)]) (hs : Same s S) :
    ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hy, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc
  obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs
  janus_run [Q]
  have hZ := lv_lt S.mem z n
  have hP : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have e : ∀ v, lv (S.mem.writeLE (s.sp.toNat + 80) 8 v) z n = lv S.mem z n := by
    intro v; unfold lv; exact Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)
  rw [hz, hn, hx, hy, e, borrow_nat]
  subst hcf
  refine ⟨htp, hdc, hex, hep, hv, ?_, ?_⟩
  · have hcl : S.flags.c.toNat ≤ 1 := by cases S.flags.c <;> simp
    by_cases hb : S.flags.c.toNat = 1
    · rw [hb] at hv ⊢
      rw [if_neg (by omega)]
    · have hb0 : 1 - S.flags.c.toNat = 1 := by omega
      rw [hb0] at hv ⊢
      rw [if_pos (by omega)]
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _ (r := (s.sp.toNat + 80, s.sp.toNat + 88)) (by simp) (Nat.le_refl _) (Nat.le_refl _)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1

theorem blk_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) :
    ∀ k (S : State) (i : Nat) (c : Bool), i + 4 * (k + 1) = n →
      S.pc = BitVec.ofNat 64 head4 → S.regs 0 = BitVec.ofNat 64 (k + 1) →
      S.regs 1 = BitVec.ofNat 64 (x + 8 * i) → S.regs 2 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 3 = BitVec.ofNat 64 (z + 8 * i) → S.flags.c = c →
      lv S.mem z i + lv s.mem y i = lv s.mem x i + 2 ^ (64 * i) * (1 - c.toNat) →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same s S →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  intro k
  induction k with
  | zero =>
    intro S i c hi hpc h0 h1 h2 h3 hcf hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    have hn4 : n = i + 4 := by omega
    subst hn4
    subst hcf
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    janus_run until [fin]
    simp only [rx0, rx1, rx2, rx3, ry0, ry1, ry2, ry3]
    refine fin_lem s hc _ _ rfl rfl (step4 s.mem S.mem z x y i S.flags.c hv) (frame_ext4 hf _ _ _ _) ?_
    same_tac hs
  | succ k ih =>
    intro S i c hi hpc h0 h1 h2 h3 hcf hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    subst hcf
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    janus_run until [head4]
    simp only [rx0, rx1, rx2, rx3, ry0, ry1, ry2, ry3]
    refine ih _ (i + 4) _ (by omega) rfl ?r0 ?r1 ?r2 ?r3 rfl (step4 s.mem S.mem z x y i S.flags.c hv)
      (frame_ext4 hf _ _ _ _) ?hs
    case r0 =>
      janus_simp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    case hs => same_tac hs
    all_goals (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem one_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) :
    ∀ j (S : State) (i : Nat) (c : Bool), i + (j + 1) = n % 4 →
      S.pc = BitVec.ofNat 64 head1 → S.regs 4 = BitVec.ofNat 64 (j + 1) → S.regs 0 = BitVec.ofNat 64 (n / 4) →
      S.regs 1 = BitVec.ofNat 64 (x + 8 * i) → S.regs 2 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 3 = BitVec.ofNat 64 (z + 8 * i) → S.flags.c = c →
      lv S.mem z i + lv s.mem y i = lv s.mem x i + 2 ^ (64 * i) * (1 - c.toNat) →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same s S →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  intro j
  induction j with
  | zero =>
    intro S i c hi hpc h4 h0 h1 h2 h3 hcf hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    subst hcf
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    rcases Nat.eq_zero_or_pos (n / 4) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus_run until [fin]
      simp only [rx0, ry0]
      refine fin_lem s hc _ _ rfl rfl (step1 s.mem S.mem z x y i S.flags.c hv) (frame_ext hf _) ?_
      same_tac hs
    · obtain ⟨q, hq'⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
      janus_run until [head4]
      simp only [rx0, ry0]
      refine blk_lem s hc q _ (i + 1) _ (by omega) rfl ?r0 ?r1 ?r2 ?r3 rfl
        (step1 s.mem S.mem z x y i S.flags.c hv) (frame_ext hf _) ?hs
      case r0 => janus_simp; rw [hq']
      case hs => same_tac hs
      all_goals (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  | succ j ih =>
    intro S i c hi hpc h4 h0 h1 h2 h3 hcf hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    subst hcf
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    janus_run until [head1]
    simp only [rx0, ry0]
    refine ih _ (i + 1) _ (by omega) rfl ?s4 ?s0 ?s1 ?s2 ?s3 rfl (step1 s.mem S.mem z x y i S.flags.c hv)
      (frame_ext hf _) ?ss
    case s4 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case s0 => janus_simp
    case ss => same_tac hs
    all_goals (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

/-- `SUBS x, x, ZR` sets `C` (no borrow) -/
theorem subs_zero_c (v : BitVec 64) : (addSub v 0#64 true).snd.c = true := by
  have := v.isLt
  simp only [addSub, ↓reduceIte, addWithCarry, BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true]
  simp only [Nat.zero_mod, decide_eq_true_eq, ne_eq]
  omega

theorem main_lem {z x y n : Nat} (s : State) (hc : Ctx s z x y n) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have hn64 : n < 2 ^ 64 := by omega
  have hz0 : lv s.mem z 0 + lv s.mem y 0 = lv s.mem x 0 + 2 ^ (64 * 0) * (1 - (true : Bool).toNat) := by
    simp [lv_zero]
  have hs0 : Same s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hmod := lsr2_mod n hn64
  janus_run until [head1, head4, fin]
  · rw [hmod] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    refine fin_lem s hc _ _ rfl (subs_zero_c _) hz0 (MemFrame.refl _ _) ?_
    same_tac hs0
  · rw [hmod] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
    refine blk_lem s hc q _ 0 _ (by omega) rfl ?r0 ?r1 ?r2 ?r3 (subs_zero_c _) hz0 (MemFrame.refl _ _) ?hs
    case r0 =>
      janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [lsr2_toNat n hn64, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hs => same_tac hs0
    all_goals janus_simp
  · obtain ⟨j, hj⟩ : ∃ j, n % 4 = j + 1 := ⟨n % 4 - 1, by omega⟩
    refine one_lem s hc j _ 0 _ (by omega) rfl ?t4 ?t0 ?t1 ?t2 ?t3 (subs_zero_c _) hz0 (MemFrame.refl _ _) ?ts
    case t4 =>
      janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case t0 =>
      janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [lsr2_toNat n hn64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case ts => same_tac hs0
    all_goals janus_simp

/-- `subVV.abi0` as a callee (library summary: transfers to any program containing these bytes at this address). -/
theorem subVV_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`z, x, y` slice bases, `zl` the length of `z`) -/
theorem ensures (z zl zc x xl xc y yl yc : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, y, yl, yc] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 80) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat + lv s.mem y.toNat zl.toNat =
          lv s.mem x.toNat zl.toNat +
            2 ^ (64 * zl.toNat) * (if lv s.mem x.toNat zl.toNat < lv s.mem y.toNat zl.toNat then 1 else 0) ∧
        results0 s s' 9 1 =
          [BitVec.ofNat 64 (if lv s.mem x.toNat zl.toNat < lv s.mem y.toNat zl.toNat then 1 else 0)] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 80, s.sp.toNat + 88)]) := by
  refine Ensures0.of_summary0 subVV_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, alx, aly, azr⟩
    have h1 := hret.aligned
    have h2 := hret.user
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6
    unfold Pre
    rw [a0, a3, a6, a1]
    refine ⟨a0, a1, a3, a6, ?_, ?_, hs.spAligned, hs.frame_bound, hs.frame_accessible, hz1, hx1, hy1, alx, aly, azr⟩
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6
    unfold Q at hq
    rw [a0, a3, a6, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    rw [q2] at q1
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [show s.sp.toNat + 8 + 8 * 9 = s.sp.toNat + 80 by omega, q2]

end FvModexp.Arm64.SubVVSum
