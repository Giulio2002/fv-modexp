import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmTac
import FvModexp.Proofs.Common.AsmMul
import FvModexp.Proofs.Lib.AddMulVVWWAmd64

/-!
# `math/big.addMulVVWW(z, x, y []Word, m, a Word) (c Word)` (go-bigmodexpfix arith_amd64.s, Go assembly ABI0, amd64)

```
z[0:n] = x[0:n] + y[0:n]·m + a   (n = len(z)),   c = the carry word out of limb n-1
```

Two code paths, selected by the runtime global `·hasADX` (a byte of `.noptrbss`, `adxAddr`; set at start-up from
CPUID): the `MULQ` path (1x loop for `n mod 4` limbs, 4x loop) and the ADX path (`MULXQ`/`ADCXQ`/`ADOXQ`, 1x loop for
`n mod 8`, 8x loop). **The summary covers both** (`addMulVVWW_summary`): its precondition only asks the flag byte to be
readable, whatever its value.

From any state at the entry whose frame words (`z, len, cap, x, len, cap, y, len, cap, m, a`, result word 11, above
the return address) describe `x[0:n]`, `y[0:n]` readable and `z[0:n]` writable, `z` equal to or disjoint from `x` and
from `y` (call sites natmul.go:129/155, nat.go:201/203: always `z == x`, `y` disjoint), and `z[0:n]` disjoint from
the call frame: the function returns (`RET`) with `Σ z_i 2^(64 i) + 2^(64 n)·c = X + Y·m + a` (values before the call),
memory changed only in `z[0:n]` and the result word.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.AddMulVVWWAmd64 (program entry)

namespace FvModexp.Amd64.AddMulVVWWSum

/-- the address of `math/big.hasADX` in the pinned harness (`Extracted.dataAddr.«…hasADX»` of the extraction) -/
abbrev adxAddr : Nat := 0xbb6b8a

abbrev head1 : Nat := entry + 0x3b
abbrev head4 : Nat := entry + 0x70
abbrev fin : Nat := entry + 0xf7
abbrev ahead1 : Nat := entry + 0x132
abbrev ahead8 : Nat := entry + 0x176
abbrev afin : Nat := entry + 0x253

structure Ctx (s : State) (z x y n m a : Nat) : Prop where
  hz : s.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  hn : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  hx : s.mem.readLE ((s.regs 4).toNat + 32) 8 = x
  hy : s.mem.readLE ((s.regs 4).toNat + 56) 8 = y
  hm : s.mem.readLE ((s.regs 4).toNat + 80) 8 = m
  ha : s.mem.readLE ((s.regs 4).toNat + 88) 8 = a
  hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  fb : (s.regs 4).toNat + 104 ≤ 2 ^ 48
  facc : s.mem.accessible (s.regs 4).toNat 104 true = true
  adx : s.mem.accessible adxAddr 1 false = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azf : Apart z (8 * n) (s.regs 4).toNat 104

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)
    (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)
    (s.mem.readLE ((s.regs 4).toNat + 80) 8) (s.mem.readLE ((s.regs 4).toNat + 88) 8)

/-- the memory after the call: `Z + 2^(64 n)·c = X + Y·m + a` -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
      2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) * m.readLE ((s.regs 4).toNat + 96) 8 =
    lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
      lv s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) *
        s.mem.readLE ((s.regs 4).toNat + 80) 8 + s.mem.readLE ((s.regs 4).toNat + 88) 8 ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]

theorem rd_frame {m m' : Memory} {z i x n a : Nat} (hf : MemFrame m m' [(z, z + 8 * i)])
    (hal : z = x ∨ Apart z (8 * n) x (8 * n)) (hin : x + 8 * i ≤ a) (hle : a + 8 ≤ x + 8 * n) (hi : i ≤ n) :
    m'.readLE a 8 = m.readLE a 8 :=
  hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hal; omega)

/-! ### one limb: `t = y·m + c`, then `+ x` (both paths compute the same Nat terms) -/

/-- the stored value (before the store reduces it mod `2^64`) of a limb with product `p`, carry-in `c`, addend `a` -/
def amr (p c a : Nat) : Nat := (p % 18446744073709551616 + c) % 18446744073709551616 + a
/-- the carry word out of that limb -/
def amc (p c a : Nat) : Nat := p / 18446744073709551616 +
  (decide (18446744073709551616 ≤ p % 18446744073709551616 + c)).toNat +
  (decide (18446744073709551616 ≤ (p % 18446744073709551616 + c) % 18446744073709551616 + a)).toNat

theorem am1 (p c a : Nat) (hp : p ≤ 18446744073709551615 * 18446744073709551615) (hc : c < 18446744073709551616)
    (ha : a < 18446744073709551616) :
    amr p c a % 18446744073709551616 + 18446744073709551616 * amc p c a = a + p + c ∧ amc p c a < 18446744073709551616 := by
  unfold amr amc
  have e : 18446744073709551615 * 18446744073709551615 = 340282366920938463426481119284349108225 := by decide
  have hq : p / 18446744073709551616 < 18446744073709551616 - 1 := Nat.div_lt_of_lt_mul (by omega)
  have h1 := Nat.mod_add_div p 18446744073709551616
  have h3 : p % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  generalize p % 18446744073709551616 = r at *
  generalize p / 18446744073709551616 = q at *
  by_cases h : 18446744073709551616 ≤ r + c
  · rw [decide_eq_true h, Bool.toNat_true]
    by_cases h' : 18446744073709551616 ≤ (r + c) % 18446744073709551616 + a
    · rw [decide_eq_true h', Bool.toNat_true]; omega
    · rw [decide_eq_false h', Bool.toNat_false]; omega
  · rw [decide_eq_false h, Bool.toNat_false]
    by_cases h' : 18446744073709551616 ≤ (r + c) % 18446744073709551616 + a
    · rw [decide_eq_true h', Bool.toNat_true]; omega
    · rw [decide_eq_false h', Bool.toNat_false]; omega

theorem prod_le (b m : Nat) (hb : b < 2 ^ 64) (hm : m < 2 ^ 64) : b * m ≤ 18446744073709551615 * 18446744073709551615 :=
  Nat.mul_le_mul (by omega) (by omega)

/-- the invariant step of one limb (product `p = y_i·m`, in either operand order) -/
theorem step1 (m0 m' : Memory) (z x y i mv a C p : Nat) (hm : mv < 2 ^ 64) (hC : C < 2 ^ 64)
    (hp : p = m0.readLE (y + 8 * i) 8 * mv)
    (hv : lv m' z i + 2 ^ (64 * i) * C = lv m0 x i + lv m0 y i * mv + a)
    (v : Nat) (hvv : v % 2 ^ 64 = amr p C (m0.readLE (x + 8 * i) 8) % 2 ^ 64) :
    lv (m'.writeLE (z + 8 * i) 8 v) z (i + 1) +
        2 ^ (64 * (i + 1)) * amc p C (m0.readLE (x + 8 * i) 8) = lv m0 x (i + 1) + lv m0 y (i + 1) * mv + a ∧
      amc p C (m0.readLE (x + 8 * i) 8) < 2 ^ 64 := by
  obtain ⟨k, hk⟩ := am1 p C (m0.readLE (x + 8 * i) 8) (hp ▸ prod_le _ _ (limb_lt _ _) hm) hC (limb_lt _ _)
  refine ⟨?_, hk⟩
  rw [lv_write_succ, lv_succ m0 x, lv_succ m0 y, pow_succ64, hvv]
  subst hp
  exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv (by omega)

theorem fin_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) (S : State) (r : Nat) (C : Nat)
    (hpc : S.rip = BitVec.ofNat 64 fin ∨ S.rip = BitVec.ofNat 64 afin) (hr : S.regs r = BitVec.ofNat 64 C)
    (hrr : r = 6 ∧ S.rip = BitVec.ofNat 64 fin ∨ r = 3 ∧ S.rip = BitVec.ofNat 64 afin) (hC : C < 2 ^ 64)
    (hv : lv S.mem z n + 2 ^ (64 * n) * C = lv s.mem x n + lv s.mem y n * m + a)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * n)]) (hs : Same64 s S) :
    ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  obtain ⟨hz, hn, hx, hy, hm, ha, hr', hfb, hfacc, hadx, accz, accx, accy, alx, aly, azf⟩ := hc
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs
  unfold Apart at azf
  have hra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have e : ∀ v, lv (S.mem.writeLE ((s.regs 4).toNat + 96) 8 v) z n = lv S.mem z n := by
    intro v; unfold lv; exact Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  rcases hrr with ⟨rfl, hpc'⟩ | ⟨rfl, hpc'⟩
  all_goals
    janus64_run [Q]
    rw [e]
    refine ⟨hfs, hfw, h87, hv, ?_⟩
    refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _
      (r := ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)) (by simp) (Nat.le_refl _) (by omega)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1

theorem modre (p c b : Nat) :
    (p % 2 ^ 64 + (c + b) % 2 ^ 64) % 2 ^ 64 = ((p % 2 ^ 64 + c) % 2 ^ 64 + b) % 2 ^ 64 := by omega

theorem tele4 (r0 r1 r2 r3 c1 c2 c3 c4 b0 b1 b2 b3 p0 p1 p2 p3 C : Nat)
    (e0 : r0 + 2 ^ 64 * c1 = b0 + p0 + C) (e1 : r1 + 2 ^ 64 * c2 = b1 + p1 + c1)
    (e2 : r2 + 2 ^ 64 * c3 = b2 + p2 + c2) (e3 : r3 + 2 ^ 64 * c4 = b3 + p3 + c3) :
    r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * r3 + 2 ^ 256 * c4 =
      (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) + (p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3) + C := by
  omega

/-- four chained limbs (the 4x block of the `MULQ` path): stored values as the executor leaves them -/
theorem amblk4 (a0 a1 a2 a3 b0 b1 b2 b3 m C c1 c2 c3 c4 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64)
    (hb3 : b3 < 2 ^ 64) (hm : m < 2 ^ 64) (hC : C < 2 ^ 64)
    (h1 : c1 = amc (a0 * m) C b0) (h2 : c2 = amc (a1 * m) c1 b1) (h3 : c3 = amc (a2 * m) c2 b2)
    (h4 : c4 = amc (a3 * m) c3 b3) :
    (a0 * m % 2 ^ 64 + (C + b0) % 2 ^ 64) % 2 ^ 64 + 2 ^ 64 * ((a1 * m % 2 ^ 64 + (c1 + b1) % 2 ^ 64) % 2 ^ 64) +
      2 ^ 128 * ((a2 * m % 2 ^ 64 + (c2 + b2) % 2 ^ 64) % 2 ^ 64) +
      2 ^ 192 * ((a3 * m % 2 ^ 64 + (c3 + b3) % 2 ^ 64) % 2 ^ 64) + 2 ^ 256 * c4 =
    (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) + (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) * m + C ∧
    c4 < 2 ^ 64 := by
  obtain ⟨e0, k0⟩ := am1 (a0 * m) C b0 (prod_le _ _ ha0 hm) hC hb0
  rw [← h1] at e0 k0
  obtain ⟨e1, k1⟩ := am1 (a1 * m) c1 b1 (prod_le _ _ ha1 hm) k0 hb1
  rw [← h2] at e1 k1
  obtain ⟨e2, k2⟩ := am1 (a2 * m) c2 b2 (prod_le _ _ ha2 hm) k1 hb2
  rw [← h3] at e2 k2
  obtain ⟨e3, k3⟩ := am1 (a3 * m) c3 b3 (prod_le _ _ ha3 hm) k2 hb3
  rw [← h4] at e3 k3
  unfold amr at e0 e1 e2 e3
  refine ⟨?_, k3⟩
  have f0 := modre (a0 * m) C b0
  have f1 := modre (a1 * m) c1 b1
  have f2 := modre (a2 * m) c2 b2
  have f3 := modre (a3 * m) c3 b3
  rw [f0, f1, f2, f3]
  rw [tele4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3]
  simp only [Nat.add_mul, Nat.mul_assoc]

/-- the value of four chained limbs, stored values in `amr` form -/
theorem blkval4 (a0 a1 a2 a3 b0 b1 b2 b3 m C c1 c2 c3 c4 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64)
    (hb3 : b3 < 2 ^ 64) (hm : m < 2 ^ 64) (hC : C < 2 ^ 64)
    (h1 : c1 = amc (a0 * m) C b0) (h2 : c2 = amc (a1 * m) c1 b1) (h3 : c3 = amc (a2 * m) c2 b2)
    (h4 : c4 = amc (a3 * m) c3 b3) :
    amr (a0 * m) C b0 % 2 ^ 64 + 2 ^ 64 * (amr (a1 * m) c1 b1 % 2 ^ 64) + 2 ^ 128 * (amr (a2 * m) c2 b2 % 2 ^ 64) +
      2 ^ 192 * (amr (a3 * m) c3 b3 % 2 ^ 64) + 2 ^ 256 * c4 =
    (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) + (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) * m + C ∧
    c1 < 2 ^ 64 ∧ c2 < 2 ^ 64 ∧ c3 < 2 ^ 64 ∧ c4 < 2 ^ 64 := by
  obtain ⟨e0, k0⟩ := am1 (a0 * m) C b0 (prod_le _ _ ha0 hm) hC hb0
  rw [← h1] at e0 k0
  obtain ⟨e1, k1⟩ := am1 (a1 * m) c1 b1 (prod_le _ _ ha1 hm) k0 hb1
  rw [← h2] at e1 k1
  obtain ⟨e2, k2⟩ := am1 (a2 * m) c2 b2 (prod_le _ _ ha2 hm) k1 hb2
  rw [← h3] at e2 k2
  obtain ⟨e3, k3⟩ := am1 (a3 * m) c3 b3 (prod_le _ _ ha3 hm) k2 hb3
  rw [← h4] at e3 k3
  refine ⟨?_, k0, k1, k2, k3⟩
  rw [tele4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3]
  simp only [Nat.add_mul, Nat.mul_assoc]

/-- limb 0 of the `MULQ` 4x block, `entry+0x70` → `entry+0x8a` -/
theorem segM0 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m C xv yv : Nat) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hC : C < 2 ^ 64) (hxv : xv < 2 ^ 64) (hyv : yv < 2 ^ 64) (hi : i + 4 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x70)) (h3 : S.regs 3 = BitVec.ofNat 64 m)
    (h6 : S.regs 6 = BitVec.ofNat 64 C) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdx : M.readLE (x + 8 * i) 8 = xv) (h_rdy : M.readLE (y + 8 * i) 8 = yv)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (v : Nat), S'.rip = BitVec.ofNat 64 (entry + 0x8a) → S'.regs 3 = BitVec.ofNat 64 m →
      S'.regs 6 = BitVec.ofNat 64 (amc (yv * m) C xv) → S'.regs 7 = S.regs 7 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) → v % 2 ^ 64 = amr (yv * m) C xv % 2 ^ 64 →
      S'.mem = M.writeLE (z + 8 * i) 8 v → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0x8a]
  refine hk _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mod_eq_of_lt hyv]
  all_goals first | (with_reducible rfl) | janus_assumption | (simp only [amc]; done) | (unfold amr; exact modre _ _ _)

/-- limb 1 of the `MULQ` 4x block, `entry+0x8a` → `entry+0xa7` -/
theorem segM1 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m C xv yv : Nat) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hC : C < 2 ^ 64) (hxv : xv < 2 ^ 64) (hyv : yv < 2 ^ 64) (hi : i + 4 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x8a)) (h3 : S.regs 3 = BitVec.ofNat 64 m)
    (h6 : S.regs 6 = BitVec.ofNat 64 C) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdx : M.readLE (x + 8 * i + 8) 8 = xv) (h_rdy : M.readLE (y + 8 * i + 8) 8 = yv)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (v : Nat), S'.rip = BitVec.ofNat 64 (entry + 0xa7) → S'.regs 3 = BitVec.ofNat 64 m →
      S'.regs 6 = BitVec.ofNat 64 (amc (yv * m) C xv) → S'.regs 7 = S.regs 7 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) → v % 2 ^ 64 = amr (yv * m) C xv % 2 ^ 64 →
      S'.mem = M.writeLE (z + 8 * i + 8) 8 v → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0xa7]
  refine hk _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mod_eq_of_lt hyv]
  all_goals first | (with_reducible rfl) | janus_assumption | (simp only [amc]; done) | (unfold amr; exact modre _ _ _)

/-- limb 2 of the `MULQ` 4x block, `entry+0xa7` → `entry+0xc4` -/
theorem segM2 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m C xv yv : Nat) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hC : C < 2 ^ 64) (hxv : xv < 2 ^ 64) (hyv : yv < 2 ^ 64) (hi : i + 4 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0xa7)) (h3 : S.regs 3 = BitVec.ofNat 64 m)
    (h6 : S.regs 6 = BitVec.ofNat 64 C) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdx : M.readLE (x + 8 * i + 16) 8 = xv) (h_rdy : M.readLE (y + 8 * i + 16) 8 = yv)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (v : Nat), S'.rip = BitVec.ofNat 64 (entry + 0xc4) → S'.regs 3 = BitVec.ofNat 64 m →
      S'.regs 6 = BitVec.ofNat 64 (amc (yv * m) C xv) → S'.regs 7 = S.regs 7 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) → v % 2 ^ 64 = amr (yv * m) C xv % 2 ^ 64 →
      S'.mem = M.writeLE (z + 8 * i + 16) 8 v → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0xc4]
  refine hk _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mod_eq_of_lt hyv]
  all_goals first | (with_reducible rfl) | janus_assumption | (simp only [amc]; done) | (unfold amr; exact modre _ _ _)

/-- limb 3 of the `MULQ` 4x block, `entry+0xc4` → `entry+0xe1` -/
theorem segM3 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m C xv yv : Nat) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hC : C < 2 ^ 64) (hxv : xv < 2 ^ 64) (hyv : yv < 2 ^ 64) (hi : i + 4 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0xc4)) (h3 : S.regs 3 = BitVec.ofNat 64 m)
    (h6 : S.regs 6 = BitVec.ofNat 64 C) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdx : M.readLE (x + 8 * i + 24) 8 = xv) (h_rdy : M.readLE (y + 8 * i + 24) 8 = yv)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (v : Nat), S'.rip = BitVec.ofNat 64 (entry + 0xe1) → S'.regs 3 = BitVec.ofNat 64 m →
      S'.regs 6 = BitVec.ofNat 64 (amc (yv * m) C xv) → S'.regs 7 = S.regs 7 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) → v % 2 ^ 64 = amr (yv * m) C xv % 2 ^ 64 →
      S'.mem = M.writeLE (z + 8 * i + 24) 8 v → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0xe1]
  refine hk _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mod_eq_of_lt hyv]
  all_goals first | (with_reducible rfl) | janus_assumption | (simp only [amc]; done) | (unfold amr; exact modre _ _ _)

theorem blk_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) :
    ∀ k (S : State) (i C : Nat), i + 4 * (k + 1) = n → C < 2 ^ 64 →
      S.rip = BitVec.ofNat 64 (entry + 0x70) → S.regs 7 = BitVec.ofNat 64 (k + 1) →
      S.regs 3 = BitVec.ofNat 64 m → S.regs 6 = BitVec.ofNat 64 C →
      S.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * C = lv s.mem x i + lv s.mem y i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same64 s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hm, ha, hr, hfb, hfacc, hadx, accz, accx, accy, alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have by' := Arm64.Memory.accessible_bound _ accy
  have hm64 : m < 2 ^ 64 := hm ▸ FvModexp.Asm.limb_lt _ _
  intro k
  induction k with
  | zero =>
    intro S i C hi hC hpc h7 h3 h6 h8 h9 h10 hv hf hs
    have hn4 : n = i + 4 := by omega
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    have hdx10 : x + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 8 := by unfold Apart at alx; omega
    have hdx20 : x + 8 * i + 16 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 16 := by unfold Apart at alx; omega
    have hdx21 : x + 8 * i + 16 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ x + 8 * i + 16 := by unfold Apart at alx; omega
    have hdx30 : x + 8 * i + 24 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 24 := by unfold Apart at alx; omega
    have hdx31 : x + 8 * i + 24 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ x + 8 * i + 24 := by unfold Apart at alx; omega
    have hdx32 : x + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ x + 8 * i + 24 := by unfold Apart at alx; omega
    have hdy10 : y + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 8 := by unfold Apart at aly; omega
    have hdy20 : y + 8 * i + 16 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 16 := by unfold Apart at aly; omega
    have hdy21 : y + 8 * i + 16 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ y + 8 * i + 16 := by unfold Apart at aly; omega
    have hdy30 : y + 8 * i + 24 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 24 := by unfold Apart at aly; omega
    have hdy31 : y + 8 * i + 24 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ y + 8 * i + 24 := by unfold Apart at aly; omega
    have hdy32 : y + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ y + 8 * i + 24 := by unfold Apart at aly; omega
    have hfn : MemFrame s.mem S.mem [(z, z + 8 * n)] := frame_mono hf (fun a n' h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hy0 := FvModexp.Asm.limb_lt s.mem (y + 8 * i); have hx0 := FvModexp.Asm.limb_lt s.mem (x + 8 * i)
    have hy1 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 8); have hx1 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 8)
    have hy2 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 16); have hx2 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 16)
    have hy3 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 24); have hx3 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 24)
    obtain ⟨hval, k1, k2, k3, k4⟩ := blkval4 _ _ _ _ _ _ _ _ m C _ _ _ _ hy0 hy1 hy2 hy3 hx0 hx1 hx2 hx3 hm64 hC rfl rfl rfl rfl
    refine segM0 s _ _ x y z i n m C _ _ _ S hm64 hC hx0 hy0 (by omega) bz bx by' accz accx accy hfn hpc h3 h6 h8 h9 h10 rfl
      (by rw [rx0]) (by rw [ry0]) hs ?_
    intro S1 v0 hpc1 h31 h61 h71 h81 h91 h101 hv0 hm1 hs1
    have hf1 : MemFrame s.mem (S.mem.writeLE (z + 8 * i) 8 v0) [(z, z + 8 * n)] := MemFrame.writeLE hfn _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
    refine segM1 s _ _ x y z i n m _ _ _ _ S1 hm64 k1 hx1 hy1 (by omega) bz bx by' accz accx accy hf1 hpc1 h31 h61 h81 h91 h101 hm1
      (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx1]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry1]) hs1 ?_
    intro S2 v1 hpc2 h32 h62 h72 h82 h92 h102 hv1 hm2 hs2
    have hf2 : MemFrame s.mem ((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1) [(z, z + 8 * n)] := MemFrame.writeLE hf1 _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
    refine segM2 s _ _ x y z i n m _ _ _ _ S2 hm64 k2 hx2 hy2 (by omega) bz bx by' accz accx accy hf2 hpc2 h32 h62 h82 h92 h102 hm2
      (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx2]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry2]) hs2 ?_
    intro S3 v2 hpc3 h33 h63 h73 h83 h93 h103 hv2 hm3 hs3
    have hf3 : MemFrame s.mem (((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2) [(z, z + 8 * n)] := MemFrame.writeLE hf2 _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
    refine segM3 s _ _ x y z i n m _ _ _ _ S3 hm64 k3 hx3 hy3 (by omega) bz bx by' accz accx accy hf3 hpc3 h33 h63 h83 h93 h103 hm3
      (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx3]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry3]) hs3 ?_
    intro S4 v3 hpc4 h34 h64 h74 h84 h94 h104 hv3 hm4 hs4
    have hf4 : MemFrame s.mem S.mem [(z, z + 8 * i)] := hf
    have hvb : lv S4.mem z (i + 4) + 2 ^ (64 * (i + 4)) * amc (s.mem.readLE (y + 8 * i + 24) 8 * m) (amc (s.mem.readLE (y + 8 * i + 16) 8 * m) (amc (s.mem.readLE (y + 8 * i + 8) 8 * m) (amc (s.mem.readLE (y + 8 * i) 8 * m) C (s.mem.readLE (x + 8 * i) 8)) (s.mem.readLE (x + 8 * i + 8) 8)) (s.mem.readLE (x + 8 * i + 16) 8)) (s.mem.readLE (x + 8 * i + 24) 8) = lv s.mem x (i + 4) + lv s.mem y (i + 4) * m + a := by
      rw [hm4, lv_write4, hv0, hv1, hv2, hv3, lv_add4 s.mem x, lv_add4 s.mem y, pow_i4]
      exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv hval
    have hfz : MemFrame s.mem S4.mem [(z, z + 8 * (i + 4))] := by rw [hm4]; exact frame_ext4 hf _ _ _ _
    have h74 : S4.regs 7 = S.regs 7 := by rw [h74, h73, h72, h71]
    rw [hm4] at hvb hfz
    subst hn4
    janus64_run until [fin]
    exact fin_lem s hc _ 6 _ (Or.inl rfl) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [h64])
      (Or.inl ⟨rfl, rfl⟩) k4 hvb hfz (by same64_tac hs4)
  | succ k ih =>
    intro S i C hi hC hpc h7 h3 h6 h8 h9 h10 hv hf hs
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have rx1 := rd_frame (a := x + 8 * i + 8) hf alx (by omega) (by omega) (by omega)
    have rx2 := rd_frame (a := x + 8 * i + 16) hf alx (by omega) (by omega) (by omega)
    have rx3 := rd_frame (a := x + 8 * i + 24) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have ry1 := rd_frame (a := y + 8 * i + 8) hf aly (by omega) (by omega) (by omega)
    have ry2 := rd_frame (a := y + 8 * i + 16) hf aly (by omega) (by omega) (by omega)
    have ry3 := rd_frame (a := y + 8 * i + 24) hf aly (by omega) (by omega) (by omega)
    have hdx10 : x + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 8 := by unfold Apart at alx; omega
    have hdx20 : x + 8 * i + 16 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 16 := by unfold Apart at alx; omega
    have hdx21 : x + 8 * i + 16 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ x + 8 * i + 16 := by unfold Apart at alx; omega
    have hdx30 : x + 8 * i + 24 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 24 := by unfold Apart at alx; omega
    have hdx31 : x + 8 * i + 24 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ x + 8 * i + 24 := by unfold Apart at alx; omega
    have hdx32 : x + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ x + 8 * i + 24 := by unfold Apart at alx; omega
    have hdy10 : y + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 8 := by unfold Apart at aly; omega
    have hdy20 : y + 8 * i + 16 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 16 := by unfold Apart at aly; omega
    have hdy21 : y + 8 * i + 16 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ y + 8 * i + 16 := by unfold Apart at aly; omega
    have hdy30 : y + 8 * i + 24 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 24 := by unfold Apart at aly; omega
    have hdy31 : y + 8 * i + 24 + 8 ≤ z + 8 * i + 8 ∨ z + 8 * i + 8 + 8 ≤ y + 8 * i + 24 := by unfold Apart at aly; omega
    have hdy32 : y + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ y + 8 * i + 24 := by unfold Apart at aly; omega
    have hfn : MemFrame s.mem S.mem [(z, z + 8 * n)] := frame_mono hf (fun a n' h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hy0 := FvModexp.Asm.limb_lt s.mem (y + 8 * i); have hx0 := FvModexp.Asm.limb_lt s.mem (x + 8 * i)
    have hy1 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 8); have hx1 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 8)
    have hy2 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 16); have hx2 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 16)
    have hy3 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 24); have hx3 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 24)
    obtain ⟨hval, k1, k2, k3, k4⟩ := blkval4 _ _ _ _ _ _ _ _ m C _ _ _ _ hy0 hy1 hy2 hy3 hx0 hx1 hx2 hx3 hm64 hC rfl rfl rfl rfl
    refine segM0 s _ _ x y z i n m C _ _ _ S hm64 hC hx0 hy0 (by omega) bz bx by' accz accx accy hfn hpc h3 h6 h8 h9 h10 rfl
      (by rw [rx0]) (by rw [ry0]) hs ?_
    intro S1 v0 hpc1 h31 h61 h71 h81 h91 h101 hv0 hm1 hs1
    have hf1 : MemFrame s.mem (S.mem.writeLE (z + 8 * i) 8 v0) [(z, z + 8 * n)] := MemFrame.writeLE hfn _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
    refine segM1 s _ _ x y z i n m _ _ _ _ S1 hm64 k1 hx1 hy1 (by omega) bz bx by' accz accx accy hf1 hpc1 h31 h61 h81 h91 h101 hm1
      (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx1]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry1]) hs1 ?_
    intro S2 v1 hpc2 h32 h62 h72 h82 h92 h102 hv1 hm2 hs2
    have hf2 : MemFrame s.mem ((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1) [(z, z + 8 * n)] := MemFrame.writeLE hf1 _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
    refine segM2 s _ _ x y z i n m _ _ _ _ S2 hm64 k2 hx2 hy2 (by omega) bz bx by' accz accx accy hf2 hpc2 h32 h62 h82 h92 h102 hm2
      (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx2]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry2]) hs2 ?_
    intro S3 v2 hpc3 h33 h63 h73 h83 h93 h103 hv2 hm3 hs3
    have hf3 : MemFrame s.mem (((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2) [(z, z + 8 * n)] := MemFrame.writeLE hf2 _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
    refine segM3 s _ _ x y z i n m _ _ _ _ S3 hm64 k3 hx3 hy3 (by omega) bz bx by' accz accx accy hf3 hpc3 h33 h63 h83 h93 h103 hm3
      (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx3]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry3]) hs3 ?_
    intro S4 v3 hpc4 h34 h64 h74 h84 h94 h104 hv3 hm4 hs4
    have hf4 : MemFrame s.mem S.mem [(z, z + 8 * i)] := hf
    have hvb : lv S4.mem z (i + 4) + 2 ^ (64 * (i + 4)) * amc (s.mem.readLE (y + 8 * i + 24) 8 * m) (amc (s.mem.readLE (y + 8 * i + 16) 8 * m) (amc (s.mem.readLE (y + 8 * i + 8) 8 * m) (amc (s.mem.readLE (y + 8 * i) 8 * m) C (s.mem.readLE (x + 8 * i) 8)) (s.mem.readLE (x + 8 * i + 8) 8)) (s.mem.readLE (x + 8 * i + 16) 8)) (s.mem.readLE (x + 8 * i + 24) 8) = lv s.mem x (i + 4) + lv s.mem y (i + 4) * m + a := by
      rw [hm4, lv_write4, hv0, hv1, hv2, hv3, lv_add4 s.mem x, lv_add4 s.mem y, pow_i4]
      exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv hval
    have hfz : MemFrame s.mem S4.mem [(z, z + 8 * (i + 4))] := by rw [hm4]; exact frame_ext4 hf _ _ _ _
    have h74 : S4.regs 7 = S.regs 7 := by rw [h74, h73, h72, h71]
    rw [hm4] at hvb hfz
    janus64_run until [head4]
    refine ih _ (i + 4) _ (by omega) k4 rfl ?r7 ?r3 ?r6 ?r8 ?r9 ?r10 hvb hfz (by same64_tac hs4)
    case r7 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case r3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h34
    case r6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h64
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem one_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) :
    ∀ j (S : State) (i C : Nat), i + (j + 1) = n % 4 → C < 2 ^ 64 →
      S.rip = BitVec.ofNat 64 head1 → S.regs 11 = BitVec.ofNat 64 (j + 1) → S.regs 7 = BitVec.ofNat 64 (n / 4) →
      S.regs 3 = BitVec.ofNat 64 m → S.regs 6 = BitVec.ofNat 64 C →
      S.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * C = lv s.mem x i + lv s.mem y i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same64 s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hm, ha, hr, hfb, hfacc, hadx, accz, accx, accy, alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have by' := Arm64.Memory.accessible_bound _ accy
  have hm64 : m < 2 ^ 64 := hm ▸ FvModexp.Asm.limb_lt _ _
  intro j
  induction j with
  | zero =>
    intro S i C hi hC hpc h11 h7 h3 h6 h8 h9 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have hk := (am1 (s.mem.readLE (y + 8 * i) 8 * m) C (s.mem.readLE (x + 8 * i) 8)
      (prod_le _ _ (FvModexp.Asm.limb_lt _ _) hm64) hC (FvModexp.Asm.limb_lt _ _)).2
    rcases Nat.eq_zero_or_pos (n / 4) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus64_run until [fin]
      try simp only [rx0, ry0, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hC]
      refine fin_lem s hc _ 6 _ (Or.inl rfl) (by simp only [setRegF_apply, ↓reduceIte]; rfl)
        (Or.inl ⟨rfl, rfl⟩) hk ((step1 s.mem S.mem z x y i m a C _ hm64 hC rfl hv _ (by unfold amr; omega)).1)
        (frame_ext hf _) ?_
      same64_tac hs
    · obtain ⟨q, hq'⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
      janus64_run until [head4]
      try simp only [rx0, ry0, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hC]
      refine blk_lem s hc q _ (i + 1) _ (by omega) hk rfl ?r7 ?r3 ?r6 ?r8 ?r9 ?r10
        ((step1 s.mem S.mem z x y i m a C _ hm64 hC rfl hv _ (by unfold amr; omega)).1) (frame_ext hf _) (by same64_tac hs)
      case r7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [h7, hq']
      case r3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3
      case r6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rfl
      all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  | succ j ih =>
    intro S i C hi hC hpc h11 h7 h3 h6 h8 h9 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have hk := (am1 (s.mem.readLE (y + 8 * i) 8 * m) C (s.mem.readLE (x + 8 * i) 8)
      (prod_le _ _ (FvModexp.Asm.limb_lt _ _) hm64) hC (FvModexp.Asm.limb_lt _ _)).2
    janus64_run until [head1]
    try simp only [rx0, ry0, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hC]
    refine ih _ (i + 1) _ (by omega) hk rfl ?s11 ?s7 ?s3 ?s6 ?s8 ?s9 ?s10
      ((step1 s.mem S.mem z x y i m a C _ hm64 hC rfl hv _ (by unfold amr; omega)).1) (frame_ext hf _) (by same64_tac hs)
    case s11 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case s7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h7
    case s3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3
    case s6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rfl
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.AddMulVVWWSum
