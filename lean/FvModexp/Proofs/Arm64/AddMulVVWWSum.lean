import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmAddMul
import FvModexp.Proofs.Common.AsmTac
import FvModexp.Proofs.Lib.AddMulVVWWA64

/-!
# `math/big.addMulVVWW(z, x, y []Word, m, a Word) (c Word)` (go-bigmodexpfix arith_arm64.s, Go assembly ABI0, arm64)

```
z[0:n] = x[0:n] + y[0:n]·m + a   (n = len(z)),   c = the carry word out of limb n-1
```

**Summary** (`addMulVVWW_summary`, every length `n = len(z)`): from any state at the entry of `addMulVVWW.abi0` whose
frame words (`z, len, cap, x, len, cap, y, len, cap, m, a`, result word 11) describe `x[0:n]`, `y[0:n]` readable and
`z[0:n]` writable, `z` equal to or disjoint from `x` and from `y` (call sites: `addMulVVWW(z[i:], z[i:], x, d, 0)`
natmul.go:155 basicMul, natmul.go:129 basicSqr, nat.go:201/203 montgomery: always `z == x`, `y` disjoint), and `z`
disjoint from the result word: the function returns with every register but `R18`, `g`, `FP`, `SP` unspecified and

* `Σ z_i 2^(64 i) + 2^(64 n)·c = X + Y·m + a` (values BEFORE the call), i.e. `z = (X + Y·m + a) mod 2^(64 n)` and the
  result word `c = (X + Y·m + a) / 2^(64 n)`;
* memory changed only in `z[0:n]` and the result word.

Loops (arith.go:255 `addMulVVWW_g`): `n mod 8` single limbs (`addmul1`), then eight-limb blocks (`addmulblk8`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.AddMulVVWWA64 (program entry)

namespace FvModexp.Arm64.AddMulVVWWSum

abbrev head1 : Nat := entry + 0x24
abbrev head8 : Nat := entry + 0x54
abbrev fin : Nat := entry + 0x114

/-- the preconditions at the entry (frame words: `z, len, cap, x, len, cap, y, len, cap, m, a, c`) -/
structure Ctx (s : State) (z x y n m a : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hy : s.mem.readLE (s.sp.toNat + 56) 8 = y
  hm : s.mem.readLE (s.sp.toNat + 80) 8 = m
  ha : s.mem.readLE (s.sp.toNat + 88) 8 = a
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 104 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 96 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 96) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 56) 8)
    (s.mem.readLE (s.sp.toNat + 16) 8) (s.mem.readLE (s.sp.toNat + 80) 8) (s.mem.readLE (s.sp.toNat + 88) 8)

/-- the memory after the call: `Z + 2^(64 n)·c = X + Y·m + a` -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
      2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) * m.readLE (s.sp.toNat + 96) 8 =
    lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
      lv s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
        s.mem.readLE (s.sp.toNat + 80) 8 + s.mem.readLE (s.sp.toNat + 88) 8 ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 96, s.sp.toNat + 104)]

theorem rd_frame {m m' : Memory} {z i x n a : Nat} (hf : MemFrame m m' [(z, z + 8 * i)])
    (hal : z = x ∨ Apart z (8 * n) x (8 * n)) (hin : x + 8 * i ≤ a) (hle : a + 8 ≤ x + 8 * n) (hi : i ≤ n) :
    m'.readLE a 8 = m.readLE a 8 :=
  hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hal; omega)

theorem fin_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) (S : State)
    (hpc : S.pc = BitVec.ofNat 64 fin)
    (hv : lv S.mem z n + 2 ^ (64 * n) * (S.regs 1).toNat = lv s.mem x n + lv s.mem y n * m + a)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)]) (hs : SameA s S) :
    ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hy, hm, ha, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc
  obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs
  janus_run [Q]
  have e : lv (S.mem.writeLE (s.sp.toNat + 96) 8 (S.regs 1).toNat) z n = lv S.mem z n := by
    unfold lv; exact Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)
  rw [hz, hn, hx, hy, hm, ha]
  refine ⟨htp, hdc, hex, hep, ?_, ?_⟩
  · rw [e]; exact hv
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _ (r := (s.sp.toNat + 96, s.sp.toNat + 104)) (by simp) (Nat.le_refl _) (Nat.le_refl _)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1

/-- one limb: `Z + P·C = X + Y·m + a` advances by `x_i + y_i·m + C` (the forms the executor leaves: the two `ADDS`
with carry-in `false` are plain sums) -/
theorem step1 (m0 m' : Memory) (z x y i m a : Nat) (c : BitVec 64) (hm64 : m < 2 ^ 64)
    (hv : lv m' z i + 2 ^ (64 * i) * c.toNat = lv m0 x i + lv m0 y i * m + a) :
    lv (m'.writeLE (z + 8 * i) 8 ((ml (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m)).toNat + c.toNat +
        m0.readLE (x + 8 * i) 8)) z (i + 1) +
      2 ^ (64 * (i + 1)) * (addWithCarry (addWithCarry (mh (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m)) 0#64
        (cf (ml (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m)) c false)).fst 0#64
        (cf (ml (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m) + c)
          (BitVec.ofNat 64 (m0.readLE (x + 8 * i) 8)) false)).fst.toNat =
    lv m0 x (i + 1) + lv m0 y (i + 1) * m + a := by
  rw [lv_write_succ, lv_succ m0 x, lv_succ m0 y, pow_succ64]
  have key := addmul1 (m0.readLE (x + 8 * i) 8) (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m) c (limb_lt _ _) (limb_lt _ _)
  simp only [cr, cf, addWithCarry_false_fst] at key
  have e : (ml (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m) + c + BitVec.ofNat 64 (m0.readLE (x + 8 * i) 8)).toNat =
      ((ml (m0.readLE (y + 8 * i) 8) (BitVec.ofNat 64 m)).toNat + c.toNat + m0.readLE (x + 8 * i) 8) % 2 ^ 64 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (limb_lt m0 (x + 8 * i))]
    rw [Nat.mod_add_mod]
  rw [e] at key
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
  exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv key

set_option exponentiation.threshold 1024 in
theorem blk_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) :
    ∀ k (S : State) (i : Nat), i + 8 * (k + 1) = n →
      S.pc = BitVec.ofNat 64 head8 → S.regs 2 = BitVec.ofNat 64 (k + 1) → S.regs 0 = BitVec.ofNat 64 m →
      S.regs 3 = BitVec.ofNat 64 (x + 8 * i) → S.regs 4 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 5 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * (S.regs 1).toNat = lv s.mem x i + lv s.mem y i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → SameA s S →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hm, ha, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  have hm64 : m < 2 ^ 64 := hm ▸ limb_lt _ _
  intro k
  induction k with
  | zero =>
    intro S i hi hpc h2 h0 h3 h4 h5 hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    have hn8 : n = i + 8 := by omega
    subst hn8
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have rx4 := rd_frame (a := x + 8 * i + 32) hf alx (by omega) (by omega) (by omega)
    have rx5 := rd_frame (a := x + 8 * i + 40) hf alx (by omega) (by omega) (by omega)
    have rx6 := rd_frame (a := x + 8 * i + 48) hf alx (by omega) (by omega) (by omega)
    have rx7 := rd_frame (a := x + 8 * i + 56) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    have ry4 := rd_frame (a := y + 8 * i + 32) hf aly (by omega) (by omega) (by omega)
    have ry5 := rd_frame (a := y + 8 * i + 40) hf aly (by omega) (by omega) (by omega)
    have ry6 := rd_frame (a := y + 8 * i + 48) hf aly (by omega) (by omega) (by omega)
    have ry7 := rd_frame (a := y + 8 * i + 56) hf aly (by omega) (by omega) (by omega)
    janus_run until [fin]
    simp only [rx0, rx1, rx2, rx3, rx4, rx5, rx6, rx7, ry0, ry1, ry2, ry3, ry4, ry5, ry6, ry7]
    refine fin_lem s hc _ rfl ?_ (frame_ext8 hf _ _ _ _ _ _ _ _) ?_
    · rw [lv_write8, lv_add8 s.mem x, lv_add8 s.mem y]
      simp only [toNat_mod64, pow_i8]
      have key := addmulblk8 (s.mem.readLE (y + 8 * i) 8) (s.mem.readLE (y + 8 * i + 8) 8) (s.mem.readLE (y + 8 * i + 16) 8)
        (s.mem.readLE (y + 8 * i + 24) 8) (s.mem.readLE (y + 8 * i + 32) 8) (s.mem.readLE (y + 8 * i + 40) 8)
        (s.mem.readLE (y + 8 * i + 48) 8) (s.mem.readLE (y + 8 * i + 56) 8)
        (s.mem.readLE (x + 8 * i) 8) (s.mem.readLE (x + 8 * i + 8) 8) (s.mem.readLE (x + 8 * i + 16) 8)
        (s.mem.readLE (x + 8 * i + 24) 8) (s.mem.readLE (x + 8 * i + 32) 8) (s.mem.readLE (x + 8 * i + 40) 8)
        (s.mem.readLE (x + 8 * i + 48) 8) (s.mem.readLE (x + 8 * i + 56) 8)
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _)
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _)
        (BitVec.ofNat 64 m) (S.regs 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
      exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv key
    · same_tac hs
  | succ k ih =>
    intro S i hi hpc h2 h0 h3 h4 h5 hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have rx4 := rd_frame (a := x + 8 * i + 32) hf alx (by omega) (by omega) (by omega)
    have rx5 := rd_frame (a := x + 8 * i + 40) hf alx (by omega) (by omega) (by omega)
    have rx6 := rd_frame (a := x + 8 * i + 48) hf alx (by omega) (by omega) (by omega)
    have rx7 := rd_frame (a := x + 8 * i + 56) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    have ry4 := rd_frame (a := y + 8 * i + 32) hf aly (by omega) (by omega) (by omega)
    have ry5 := rd_frame (a := y + 8 * i + 40) hf aly (by omega) (by omega) (by omega)
    have ry6 := rd_frame (a := y + 8 * i + 48) hf aly (by omega) (by omega) (by omega)
    have ry7 := rd_frame (a := y + 8 * i + 56) hf aly (by omega) (by omega) (by omega)
    janus_run until [head8]
    simp only [rx0, rx1, rx2, rx3, rx4, rx5, rx6, rx7, ry0, ry1, ry2, ry3, ry4, ry5, ry6, ry7]
    refine ih _ (i + 8) (by omega) rfl ?r2 ?r0 ?r3 ?r4 ?r5 ?hv (frame_ext8 hf _ _ _ _ _ _ _ _) ?hs
    case r2 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case r0 => janus_simp
    case hv =>
      rw [lv_write8, lv_add8 s.mem x, lv_add8 s.mem y]
      simp only [toNat_mod64, pow_i8]
      have key := addmulblk8 (s.mem.readLE (y + 8 * i) 8) (s.mem.readLE (y + 8 * i + 8) 8) (s.mem.readLE (y + 8 * i + 16) 8)
        (s.mem.readLE (y + 8 * i + 24) 8) (s.mem.readLE (y + 8 * i + 32) 8) (s.mem.readLE (y + 8 * i + 40) 8)
        (s.mem.readLE (y + 8 * i + 48) 8) (s.mem.readLE (y + 8 * i + 56) 8)
        (s.mem.readLE (x + 8 * i) 8) (s.mem.readLE (x + 8 * i + 8) 8) (s.mem.readLE (x + 8 * i + 16) 8)
        (s.mem.readLE (x + 8 * i + 24) 8) (s.mem.readLE (x + 8 * i + 32) 8) (s.mem.readLE (x + 8 * i + 40) 8)
        (s.mem.readLE (x + 8 * i + 48) 8) (s.mem.readLE (x + 8 * i + 56) 8)
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _)
        (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _) (limb_lt _ _)
        (BitVec.ofNat 64 m) (S.regs 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at key
      exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv key
    case hs => same_tac hs
    all_goals (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem one_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) :
    ∀ j (S : State) (i : Nat), i + (j + 1) = n % 8 →
      S.pc = BitVec.ofNat 64 head1 → S.regs 6 = BitVec.ofNat 64 (j + 1) → S.regs 2 = BitVec.ofNat 64 (n / 8) →
      S.regs 0 = BitVec.ofNat 64 m →
      S.regs 3 = BitVec.ofNat 64 (x + 8 * i) → S.regs 4 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 5 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * (S.regs 1).toNat = lv s.mem x i + lv s.mem y i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → SameA s S →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hm, ha, hl4, hl56, hal, hfb, hfacc, accz, accx, accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have by' := Memory.accessible_bound _ accy
  have hm64 : m < 2 ^ 64 := hm ▸ limb_lt _ _
  intro j
  induction j with
  | zero =>
    intro S i hi hpc h6 h2 h0 h3 h4 h5 hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    rcases Nat.eq_zero_or_pos (n / 8) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus_run until [fin]
      simp only [rx0, ry0]
      exact fin_lem s hc _ rfl (step1 s.mem S.mem z x y i m a (S.regs 1) hm64 hv) (frame_ext hf _) (by same_tac hs)
    · obtain ⟨q, hq'⟩ : ∃ q, n / 8 = q + 1 := ⟨n / 8 - 1, by omega⟩
      janus_run until [head8]
      simp only [rx0, ry0]
      refine blk_lem s hc q _ (i + 1) (by omega) rfl ?r2 ?r0 ?r3 ?r4 ?r5 (step1 s.mem S.mem z x y i m a (S.regs 1) hm64 hv)
        (frame_ext hf _) ?hs
      case r2 => janus_simp; rw [hq']
      case r0 => janus_simp
      case hs => same_tac hs
      all_goals (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  | succ j ih =>
    intro S i hi hpc h6 h2 h0 h3 h4 h5 hv hf hs
    have hs' := hs
    obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    janus_run until [head1]
    simp only [rx0, ry0]
    refine ih _ (i + 1) (by omega) rfl ?s6 ?s2 ?s0 ?s3 ?s4 ?s5 (step1 s.mem S.mem z x y i m a (S.regs 1) hm64 hv)
      (frame_ext hf _) ?ss
    case s6 => janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case s2 => janus_simp
    case s0 => janus_simp
    case ss => same_tac hs
    all_goals (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem main_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hl4, hl56, hal, hfb, hfacc, accz, accx,
    accy, alx, aly, azr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have hm64 : m < 2 ^ 64 := h_rd_arg9 ▸ limb_lt _ _
  have ha64 : a < 2 ^ 64 := h_rd_arg10 ▸ limb_lt _ _
  have hn64 : n < 2 ^ 64 := by omega
  have hmod := lsr3_mod n hn64
  have hz0 : lv s.mem z 0 + a = lv s.mem x 0 + lv s.mem y 0 * m + a := by simp [lv_zero]
  have hs0 := SameA.refl s
  janus_run until [head1, head8, fin]
  · rw [hmod] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    refine fin_lem s hc _ rfl ?_ (frame_zero _ _) (by same_tac hs0)
    janus_simp; exact hz0
  · rw [hmod] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 8 = q + 1 := ⟨n / 8 - 1, by omega⟩
    refine blk_lem s hc q _ 0 (by omega) rfl ?r2 ?r0 ?r3 ?r4 ?r5 ?hv (frame_zero _ _) (by same_tac hs0)
    case r2 =>
      janus_simp; apply BitVec.eq_of_toNat_eq
      rw [lsr3_toNat n hn64, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hv => janus_simp; exact hz0
    all_goals janus_simp
  · obtain ⟨j, hj⟩ : ∃ j, n % 8 = j + 1 := ⟨n % 8 - 1, by omega⟩
    refine one_lem s hc j _ 0 (by omega) rfl ?t6 ?t2 ?t0 ?t3 ?t4 ?t5 ?tv (frame_zero _ _) (by same_tac hs0)
    case t6 =>
      janus_simp; apply BitVec.eq_of_toNat_eq
      rw [and7_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case t2 =>
      janus_simp; apply BitVec.eq_of_toNat_eq
      rw [lsr3_toNat n hn64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case tv => janus_simp; exact hz0
    all_goals janus_simp

/-- `addMulVVWW.abi0` as a callee (library summary: transfers to any program containing these bytes at this address). -/
theorem addMulVVWW_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame -/
theorem ensures (z zl zc x xl xc y yl yc m a : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, y, yl, yc, m, a] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 96) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat =
          (lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat * m.toNat + a.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 11 1 = [BitVec.ofNat 64
          ((lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat * m.toNat + a.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 96, s.sp.toNat + 104)]) := by
  refine Ensures0.of_summary0 addMulVVWW_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, alx, aly, azr⟩
    have h1 := hret.aligned
    have h2 := hret.user
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a9 := hs.arg (i := 9) (by simp)
    have a10 := hs.arg (i := 10) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6 a9 a10
    unfold Pre
    rw [a0, a3, a6, a9, a10, a1]
    refine ⟨a0, a1, a3, a6, a9, a10, ?_, ?_, hs.spAligned, hs.frame_bound, hs.frame_accessible, hz1, hx1, hy1,
      alx, aly, azr⟩
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a9 := hs.arg (i := 9) (by simp)
    have a10 := hs.arg (i := 10) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6 a9 a10
    unfold Q at hq
    rw [a0, a3, a6, a9, a10, a1] at hq
    obtain ⟨q1, q3⟩ := hq
    have hZ := lv_lt s'.mem z.toNat zl.toNat
    have hP : 0 < 2 ^ (64 * zl.toNat) := Nat.two_pow_pos _
    refine ⟨?_, ?_, q3⟩
    · rw [← q1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hZ]
    · simp only [results0, wordsAt_succ, wordsAt_zero, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
      rw [show s.sp.toNat + 8 + 8 * 11 = s.sp.toNat + 96 by omega, ← Nat.add_assoc (lv s.mem x.toNat zl.toNat), ← q1, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt hZ, Nat.zero_add]

end FvModexp.Arm64.AddMulVVWWSum
