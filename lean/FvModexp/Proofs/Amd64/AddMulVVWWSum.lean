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

/-! ### the ADX path: `MULXQ`, carry chains in `CF` (`ADCXQ`) and `OF` (`ADOXQ`) -/

/-- one ADX limb: `t = (m·y) mod B + H + cf` (`ADCXQ`), `u = t mod B + x + of` (`ADOXQ`) -/
theorem toNat_le_one (c : Bool) : c.toNat ≤ 1 := by cases c <;> simp

theorem adx1 (p H xa c o : Nat) (hp : p ≤ 18446744073709551615 * 18446744073709551615)
    (hH : H < 18446744073709551616) (hx : xa < 18446744073709551616) (hc : c ≤ 1) (ho : o ≤ 1) :
    ((p % 18446744073709551616 + H + c) % 18446744073709551616 + xa + o) % 18446744073709551616 +
      18446744073709551616 * (p / 18446744073709551616 +
        (decide (18446744073709551616 ≤ p % 18446744073709551616 + H + c)).toNat +
        (decide (18446744073709551616 ≤ (p % 18446744073709551616 + H + c) % 18446744073709551616 + xa + o)).toNat) =
    xa + p + (H + c + o) := by
  have e : 18446744073709551615 * 18446744073709551615 = 340282366920938463426481119284349108225 := by decide
  have hq : p / 18446744073709551616 < 18446744073709551616 - 1 := Nat.div_lt_of_lt_mul (by omega)
  have h1 := Nat.mod_add_div p 18446744073709551616
  have h3 : p % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  clear hp e
  generalize p % 18446744073709551616 = r at *
  generalize p / 18446744073709551616 = q at *
  by_cases h : 18446744073709551616 ≤ r + H + c
  · simp only [h, decide_true, Bool.toNat_true]
    by_cases h' : 18446744073709551616 ≤ (r + H + c) % 18446744073709551616 + xa + o
    · simp only [h', decide_true, Bool.toNat_true]; omega
    · simp only [h', decide_false, Bool.toNat_false]; omega
  · simp only [h, decide_false, Bool.toNat_false]
    by_cases h' : 18446744073709551616 ≤ (r + H + c) % 18446744073709551616 + xa + o
    · simp only [h', decide_true, Bool.toNat_true]; omega
    · simp only [h', decide_false, Bool.toNat_false]; omega

/-- adjacent limbs of `v` and `z` (equal or disjoint slices) do not overlap -/
theorem dpair {m m' : Memory} {z v i n : Nat} {oa : Nat} (_hf : MemFrame m m' [(z, z + 8 * i)])
    (hal : z = v ∨ Apart z (8 * n) v (8 * n)) (hb : i * 8 + oa + 16 ≤ 8 * n) :
    v + 8 * i + (oa + 8) + 8 ≤ z + 8 * i + oa ∨ z + 8 * i + oa + 8 ≤ v + 8 * i + (oa + 8) := by
  unfold Apart at hal; omega

/-- limbs 0, 1 of the ADX 8x block, `entry+0x17c` → `entry+0x1a7`: with the carry word
`W = H + cf + of` (`RBX` and the two flag chains) -/
theorem segA0 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m H xa xb ya yb : Nat) (cf of : Bool)
    (pf af zf sf : Option Bool) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hH : H < 2 ^ 64) (hxa : xa < 2 ^ 64) (hxb : xb < 2 ^ 64) (hya : ya < 2 ^ 64)
    (hyb : yb < 2 ^ 64) (hi : i + 8 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x17c)) (h2 : S.regs 2 = BitVec.ofNat 64 m)
    (h3 : S.regs 3 = BitVec.ofNat 64 H) (hfl : S.flags = ⟨some cf, pf, af, zf, sf, some of⟩)
    (h7 : S.regs 7 = 0#64) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdxa : M.readLE (x + 8 * i) 8 = xa) (h_rdya : M.readLE (y + 8 * i) 8 = ya)
    (hdx : x + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 8)
    (hdy : y + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 8)
    (h_rdxb : M.readLE (x + 8 * i + 8) 8 = xb) (h_rdyb : M.readLE (y + 8 * i + 8) 8 = yb)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (va vb H' : Nat) (cf' of' : Bool) (pf' af' zf' sf' : Option Bool),
      S'.rip = BitVec.ofNat 64 (entry + 0x1a7) → S'.regs 2 = BitVec.ofNat 64 m →
      S'.regs 3 = BitVec.ofNat 64 H' → H' < 2 ^ 64 → S'.flags = ⟨some cf', pf', af', zf', sf', some of'⟩ →
      S'.regs 6 = S.regs 6 → S'.regs 7 = 0#64 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      va % 2 ^ 64 + 2 ^ 64 * (vb % 2 ^ 64) + 2 ^ 128 * (H' + cf'.toNat + of'.toNat) =
        (xa + 2 ^ 64 * xb) + (m * ya + 2 ^ 64 * (m * yb)) + (H + cf.toNat + of.toNat) →
      S'.mem = (M.writeLE (z + 8 * i) 8 va).writeLE (z + 8 * i + 8) 8 vb → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0x1a7]
  have ea := adx1 (m * ya) H xa cf.toNat of.toNat (prod_le _ _ hm hya) hH hxa (toNat_le_one cf) (toNat_le_one of)
  have ha2 : m * ya / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hya; omega)
  have eb := adx1 (m * yb) (m * ya / 18446744073709551616) xb
    (decide (18446744073709551616 ≤ m * ya % 18446744073709551616 + H + cf.toNat)).toNat
    (decide (18446744073709551616 ≤ (m * ya % 18446744073709551616 + H + cf.toNat) % 18446744073709551616 + xa +
      of.toNat)).toNat (prod_le _ _ hm hyb) ha2 hxb (toNat_le_one _) (toNat_le_one _)
  have hb2 : m * yb / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hyb; omega)
  refine hk _ _ _ _ _ _ _ _ _ _ rfl ?_ ?_ hb2 rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | janus_assumption)
  omega

/-- limbs 2, 3 of the ADX 8x block, `entry+0x1a7` → `entry+0x1d5`: with the carry word
`W = H + cf + of` (`RBX` and the two flag chains) -/
theorem segA1 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m H xa xb ya yb : Nat) (cf of : Bool)
    (pf af zf sf : Option Bool) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hH : H < 2 ^ 64) (hxa : xa < 2 ^ 64) (hxb : xb < 2 ^ 64) (hya : ya < 2 ^ 64)
    (hyb : yb < 2 ^ 64) (hi : i + 8 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x1a7)) (h2 : S.regs 2 = BitVec.ofNat 64 m)
    (h3 : S.regs 3 = BitVec.ofNat 64 H) (hfl : S.flags = ⟨some cf, pf, af, zf, sf, some of⟩)
    (h7 : S.regs 7 = 0#64) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdxa : M.readLE (x + 8 * i + 16) 8 = xa) (h_rdya : M.readLE (y + 8 * i + 16) 8 = ya)
    (hdx : x + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ x + 8 * i + 24)
    (hdy : y + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ y + 8 * i + 24)
    (h_rdxb : M.readLE (x + 8 * i + 24) 8 = xb) (h_rdyb : M.readLE (y + 8 * i + 24) 8 = yb)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (va vb H' : Nat) (cf' of' : Bool) (pf' af' zf' sf' : Option Bool),
      S'.rip = BitVec.ofNat 64 (entry + 0x1d5) → S'.regs 2 = BitVec.ofNat 64 m →
      S'.regs 3 = BitVec.ofNat 64 H' → H' < 2 ^ 64 → S'.flags = ⟨some cf', pf', af', zf', sf', some of'⟩ →
      S'.regs 6 = S.regs 6 → S'.regs 7 = 0#64 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      va % 2 ^ 64 + 2 ^ 64 * (vb % 2 ^ 64) + 2 ^ 128 * (H' + cf'.toNat + of'.toNat) =
        (xa + 2 ^ 64 * xb) + (m * ya + 2 ^ 64 * (m * yb)) + (H + cf.toNat + of.toNat) →
      S'.mem = (M.writeLE (z + 8 * i + 16) 8 va).writeLE (z + 8 * i + 24) 8 vb → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0x1d5]
  have ea := adx1 (m * ya) H xa cf.toNat of.toNat (prod_le _ _ hm hya) hH hxa (toNat_le_one cf) (toNat_le_one of)
  have ha2 : m * ya / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hya; omega)
  have eb := adx1 (m * yb) (m * ya / 18446744073709551616) xb
    (decide (18446744073709551616 ≤ m * ya % 18446744073709551616 + H + cf.toNat)).toNat
    (decide (18446744073709551616 ≤ (m * ya % 18446744073709551616 + H + cf.toNat) % 18446744073709551616 + xa +
      of.toNat)).toNat (prod_le _ _ hm hyb) ha2 hxb (toNat_le_one _) (toNat_le_one _)
  have hb2 : m * yb / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hyb; omega)
  refine hk _ _ _ _ _ _ _ _ _ _ rfl ?_ ?_ hb2 rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | janus_assumption)
  omega

/-- limbs 4, 5 of the ADX 8x block, `entry+0x1d5` → `entry+0x203`: with the carry word
`W = H + cf + of` (`RBX` and the two flag chains) -/
theorem segA2 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m H xa xb ya yb : Nat) (cf of : Bool)
    (pf af zf sf : Option Bool) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hH : H < 2 ^ 64) (hxa : xa < 2 ^ 64) (hxb : xb < 2 ^ 64) (hya : ya < 2 ^ 64)
    (hyb : yb < 2 ^ 64) (hi : i + 8 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x1d5)) (h2 : S.regs 2 = BitVec.ofNat 64 m)
    (h3 : S.regs 3 = BitVec.ofNat 64 H) (hfl : S.flags = ⟨some cf, pf, af, zf, sf, some of⟩)
    (h7 : S.regs 7 = 0#64) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdxa : M.readLE (x + 8 * i + 32) 8 = xa) (h_rdya : M.readLE (y + 8 * i + 32) 8 = ya)
    (hdx : x + 8 * i + 40 + 8 ≤ z + 8 * i + 32 ∨ z + 8 * i + 32 + 8 ≤ x + 8 * i + 40)
    (hdy : y + 8 * i + 40 + 8 ≤ z + 8 * i + 32 ∨ z + 8 * i + 32 + 8 ≤ y + 8 * i + 40)
    (h_rdxb : M.readLE (x + 8 * i + 40) 8 = xb) (h_rdyb : M.readLE (y + 8 * i + 40) 8 = yb)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (va vb H' : Nat) (cf' of' : Bool) (pf' af' zf' sf' : Option Bool),
      S'.rip = BitVec.ofNat 64 (entry + 0x203) → S'.regs 2 = BitVec.ofNat 64 m →
      S'.regs 3 = BitVec.ofNat 64 H' → H' < 2 ^ 64 → S'.flags = ⟨some cf', pf', af', zf', sf', some of'⟩ →
      S'.regs 6 = S.regs 6 → S'.regs 7 = 0#64 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      va % 2 ^ 64 + 2 ^ 64 * (vb % 2 ^ 64) + 2 ^ 128 * (H' + cf'.toNat + of'.toNat) =
        (xa + 2 ^ 64 * xb) + (m * ya + 2 ^ 64 * (m * yb)) + (H + cf.toNat + of.toNat) →
      S'.mem = (M.writeLE (z + 8 * i + 32) 8 va).writeLE (z + 8 * i + 40) 8 vb → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0x203]
  have ea := adx1 (m * ya) H xa cf.toNat of.toNat (prod_le _ _ hm hya) hH hxa (toNat_le_one cf) (toNat_le_one of)
  have ha2 : m * ya / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hya; omega)
  have eb := adx1 (m * yb) (m * ya / 18446744073709551616) xb
    (decide (18446744073709551616 ≤ m * ya % 18446744073709551616 + H + cf.toNat)).toNat
    (decide (18446744073709551616 ≤ (m * ya % 18446744073709551616 + H + cf.toNat) % 18446744073709551616 + xa +
      of.toNat)).toNat (prod_le _ _ hm hyb) ha2 hxb (toNat_le_one _) (toNat_le_one _)
  have hb2 : m * yb / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hyb; omega)
  refine hk _ _ _ _ _ _ _ _ _ _ rfl ?_ ?_ hb2 rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | janus_assumption)
  omega

/-- limbs 6, 7 of the ADX 8x block, `entry+0x203` → `entry+0x231`: with the carry word
`W = H + cf + of` (`RBX` and the two flag chains) -/
theorem segA3 (s : State) (ret : BitVec 64) (Q : State → Prop) (x y z i n m H xa xb ya yb : Nat) (cf of : Bool)
    (pf af zf sf : Option Bool) (M : Memory) (S : State)
    (hm : m < 2 ^ 64) (hH : H < 2 ^ 64) (hxa : xa < 2 ^ 64) (hxb : xb < 2 ^ 64) (hya : ya < 2 ^ 64)
    (hyb : yb < 2 ^ 64) (hi : i + 8 ≤ n)
    (bz : z + 8 * n ≤ 2 ^ 48) (bx : x + 8 * n ≤ 2 ^ 48) (by' : y + 8 * n ≤ 2 ^ 48)
    (accz : s.mem.accessible z (8 * n) true = true) (accx : s.mem.accessible x (8 * n) false = true)
    (accy : s.mem.accessible y (8 * n) false = true) (hf : MemFrame s.mem M [(z, z + 8 * n)])
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x203)) (h2 : S.regs 2 = BitVec.ofNat 64 m)
    (h3 : S.regs 3 = BitVec.ofNat 64 H) (hfl : S.flags = ⟨some cf, pf, af, zf, sf, some of⟩)
    (h7 : S.regs 7 = 0#64) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i)) (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i))
    (hmem : S.mem = M) (h_rdxa : M.readLE (x + 8 * i + 48) 8 = xa) (h_rdya : M.readLE (y + 8 * i + 48) 8 = ya)
    (hdx : x + 8 * i + 56 + 8 ≤ z + 8 * i + 48 ∨ z + 8 * i + 48 + 8 ≤ x + 8 * i + 56)
    (hdy : y + 8 * i + 56 + 8 ≤ z + 8 * i + 48 ∨ z + 8 * i + 48 + 8 ≤ y + 8 * i + 56)
    (h_rdxb : M.readLE (x + 8 * i + 56) 8 = xb) (h_rdyb : M.readLE (y + 8 * i + 56) 8 = yb)
    (hs : Same64 s S)
    (hk : ∀ (S' : State) (va vb H' : Nat) (cf' of' : Bool) (pf' af' zf' sf' : Option Bool),
      S'.rip = BitVec.ofNat 64 (entry + 0x231) → S'.regs 2 = BitVec.ofNat 64 m →
      S'.regs 3 = BitVec.ofNat 64 H' → H' < 2 ^ 64 → S'.flags = ⟨some cf', pf', af', zf', sf', some of'⟩ →
      S'.regs 6 = S.regs 6 → S'.regs 7 = 0#64 →
      S'.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S'.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S'.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      va % 2 ^ 64 + 2 ^ 64 * (vb % 2 ^ 64) + 2 ^ 128 * (H' + cf'.toNat + of'.toNat) =
        (xa + 2 ^ 64 * xb) + (m * ya + 2 ^ 64 * (m * yb)) + (H + cf.toNat + of.toNat) →
      S'.mem = (M.writeLE (z + 8 * i + 48) 8 va).writeLE (z + 8 * i + 56) 8 vb → Same64 s S' → ReachesRet program ret S' Q) :
    ReachesRet program ret S Q := by
  have hs' := hs
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
  janus64_run until [entry + 0x231]
  have ea := adx1 (m * ya) H xa cf.toNat of.toNat (prod_le _ _ hm hya) hH hxa (toNat_le_one cf) (toNat_le_one of)
  have ha2 : m * ya / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hya; omega)
  have eb := adx1 (m * yb) (m * ya / 18446744073709551616) xb
    (decide (18446744073709551616 ≤ m * ya % 18446744073709551616 + H + cf.toNat)).toNat
    (decide (18446744073709551616 ≤ (m * ya % 18446744073709551616 + H + cf.toNat) % 18446744073709551616 + xa +
      of.toNat)).toNat (prod_le _ _ hm hyb) ha2 hxb (toNat_le_one _) (toNat_le_one _)
  have hb2 : m * yb / 18446744073709551616 < 18446744073709551616 := Nat.div_lt_of_lt_mul (by
    have := prod_le _ _ hm hyb; omega)
  refine hk _ _ _ _ _ _ _ _ _ _ rfl ?_ ?_ hb2 rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl (by same64_tac hs)
  all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | janus_assumption)
  omega

theorem ablock {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) (ret : BitVec 64) (Q' : State → Prop)
    (S : State) (i W : Nat) (hi : i + 8 ≤ n) (hW : W < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 ahead8) (h2 : S.regs 2 = BitVec.ofNat 64 m) (h3 : S.regs 3 = BitVec.ofNat 64 W)
    (h7 : S.regs 7 = 0#64) (h8 : S.regs 8 = BitVec.ofNat 64 (x + 8 * i)) (h9 : S.regs 9 = BitVec.ofNat 64 (y + 8 * i))
    (h10 : S.regs 10 = BitVec.ofNat 64 (z + 8 * i)) (hf : MemFrame s.mem S.mem [(z, z + 8 * i)]) (hs : Same64 s S)
    (hk : ∀ (S4 : State) (v0 v1 v2 v3 v4 v5 v6 v7 H1 H2 H3 H4 : Nat) (cf1 cf2 cf3 cf4 of1 of2 of3 of4 : Bool)
      (pf af zf sf : Option Bool),
      S4.rip = BitVec.ofNat 64 (entry + 0x231) → S4.regs 2 = BitVec.ofNat 64 m → S4.regs 3 = BitVec.ofNat 64 H4 →
      H4 < 2 ^ 64 → S4.flags = ⟨some cf4, pf, af, zf, sf, some of4⟩ → S4.regs 6 = S.regs 6 → S4.regs 7 = 0#64 →
      S4.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S4.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S4.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      S4.mem = ((((((((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2).writeLE (z + 8 * i + 24) 8 v3).writeLE (z + 8 * i + 32) 8 v4).writeLE (z + 8 * i + 40) 8 v5).writeLE (z + 8 * i + 48) 8 v6).writeLE (z + 8 * i + 56) 8 v7) → Same64 s S4 →
      v0 % 2 ^ 64 + 2 ^ 64 * (v1 % 2 ^ 64) + 2 ^ 128 * (H1 + cf1.toNat + of1.toNat) = (s.mem.readLE (x + 8 * i) 8 + 2 ^ 64 * s.mem.readLE (x + 8 * i + 8) 8) + (m * s.mem.readLE (y + 8 * i) 8 + 2 ^ 64 * (m * s.mem.readLE (y + 8 * i + 8) 8)) + W →
      v2 % 2 ^ 64 + 2 ^ 64 * (v3 % 2 ^ 64) + 2 ^ 128 * (H2 + cf2.toNat + of2.toNat) = (s.mem.readLE (x + 8 * i + 16) 8 + 2 ^ 64 * s.mem.readLE (x + 8 * i + 24) 8) + (m * s.mem.readLE (y + 8 * i + 16) 8 + 2 ^ 64 * (m * s.mem.readLE (y + 8 * i + 24) 8)) + (H1 + cf1.toNat + of1.toNat) →
      v4 % 2 ^ 64 + 2 ^ 64 * (v5 % 2 ^ 64) + 2 ^ 128 * (H3 + cf3.toNat + of3.toNat) = (s.mem.readLE (x + 8 * i + 32) 8 + 2 ^ 64 * s.mem.readLE (x + 8 * i + 40) 8) + (m * s.mem.readLE (y + 8 * i + 32) 8 + 2 ^ 64 * (m * s.mem.readLE (y + 8 * i + 40) 8)) + (H2 + cf2.toNat + of2.toNat) →
      v6 % 2 ^ 64 + 2 ^ 64 * (v7 % 2 ^ 64) + 2 ^ 128 * (H4 + cf4.toNat + of4.toNat) = (s.mem.readLE (x + 8 * i + 48) 8 + 2 ^ 64 * s.mem.readLE (x + 8 * i + 56) 8) + (m * s.mem.readLE (y + 8 * i + 48) 8 + 2 ^ 64 * (m * s.mem.readLE (y + 8 * i + 56) 8)) + (H3 + cf3.toNat + of3.toNat) →
      ReachesRet program ret S4 Q') :
    ReachesRet program ret S Q' := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hy, hm, ha, hr, hfb, hfacc, hadx, accz, accx, accy, alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have by' := Arm64.Memory.accessible_bound _ accy
  have hm64 : m < 2 ^ 64 := hm ▸ FvModexp.Asm.limb_lt _ _
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
  have hdx10 : x + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ x + 8 * i + 8 := dpair hf alx (by omega)
  have hdx32 : x + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ x + 8 * i + 24 := dpair hf alx (by omega)
  have hdx54 : x + 8 * i + 40 + 8 ≤ z + 8 * i + 32 ∨ z + 8 * i + 32 + 8 ≤ x + 8 * i + 40 := dpair hf alx (by omega)
  have hdx76 : x + 8 * i + 56 + 8 ≤ z + 8 * i + 48 ∨ z + 8 * i + 48 + 8 ≤ x + 8 * i + 56 := dpair hf alx (by omega)
  have hdy10 : y + 8 * i + 8 + 8 ≤ z + 8 * i ∨ z + 8 * i + 8 ≤ y + 8 * i + 8 := dpair hf aly (by omega)
  have hdy32 : y + 8 * i + 24 + 8 ≤ z + 8 * i + 16 ∨ z + 8 * i + 16 + 8 ≤ y + 8 * i + 24 := dpair hf aly (by omega)
  have hdy54 : y + 8 * i + 40 + 8 ≤ z + 8 * i + 32 ∨ z + 8 * i + 32 + 8 ≤ y + 8 * i + 40 := dpair hf aly (by omega)
  have hdy76 : y + 8 * i + 56 + 8 ≤ z + 8 * i + 48 ∨ z + 8 * i + 48 + 8 ≤ y + 8 * i + 56 := dpair hf aly (by omega)
  have alx' := alx
  have aly' := aly
  unfold Apart at alx' aly'
  have hfn : MemFrame s.mem S.mem [(z, z + 8 * n)] := frame_mono hf (fun a n' h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hy0 := FvModexp.Asm.limb_lt s.mem (y + 8 * i); have hx0 := FvModexp.Asm.limb_lt s.mem (x + 8 * i)
  have hy1 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 8); have hx1 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 8)
  have hy2 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 16); have hx2 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 16)
  have hy3 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 24); have hx3 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 24)
  have hy4 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 32); have hx4 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 32)
  have hy5 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 40); have hx5 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 40)
  have hy6 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 48); have hx6 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 48)
  have hy7 := FvModexp.Asm.limb_lt s.mem (y + 8 * i + 56); have hx7 := FvModexp.Asm.limb_lt s.mem (x + 8 * i + 56)
  janus64_run until [entry + 0x17c]
  refine segA0 s _ _ x y z i n m W _ _ _ _ false false _ _ _ _ _ _ hm64 hW hx0 hx1 hy0 hy1 (by omega) bz bx by' accz accx accy hfn rfl
    (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h2) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h3) rfl
    (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h7) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h8)
    (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h9) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h10) rfl
    (by rw [rx0]) (by rw [ry0]) hdx10 hdy10 (by rw [rx1]) (by rw [ry1]) (by same64_tac hs) ?_
  intro S1 v0 v1 H1 cf1 of1 pf1 af1 zf1 sf1 hpc1 h21 h31 hH1 hfl1 h61 h71 h81 h91 h101 he0 hm1 hs1
  have hf1 : MemFrame s.mem ((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1) [(z, z + 8 * n)] := MemFrame.writeLE (MemFrame.writeLE hfn _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)) _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
  refine segA1 s _ _ x y z i n m H1 _ _ _ _ cf1 of1 _ _ _ _ _ S1 hm64 hH1 hx2 hx3 hy2 hy3 (by omega) bz bx by' accz accx accy hf1 hpc1 h21 h31 hfl1
    h71 h81 h91 h101 hm1 (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx2]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry2]) hdx32 hdy32 (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx3]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry3]) hs1 ?_
  intro S2 v2 v3 H2 cf2 of2 pf2 af2 zf2 sf2 hpc2 h22 h32 hH2 hfl2 h62 h72 h82 h92 h102 he1 hm2 hs2
  have hf2 : MemFrame s.mem ((((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2).writeLE (z + 8 * i + 24) 8 v3) [(z, z + 8 * n)] := MemFrame.writeLE (MemFrame.writeLE hf1 _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)) _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
  refine segA2 s _ _ x y z i n m H2 _ _ _ _ cf2 of2 _ _ _ _ _ S2 hm64 hH2 hx4 hx5 hy4 hy5 (by omega) bz bx by' accz accx accy hf2 hpc2 h22 h32 hfl2
    h72 h82 h92 h102 hm2 (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx4]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry4]) hdx54 hdy54 (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx5]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry5]) hs2 ?_
  intro S3 v4 v5 H3 cf3 of3 pf3 af3 zf3 sf3 hpc3 h23 h33 hH3 hfl3 h63 h73 h83 h93 h103 he2 hm3 hs3
  have hf3 : MemFrame s.mem ((((((S.mem.writeLE (z + 8 * i) 8 v0).writeLE (z + 8 * i + 8) 8 v1).writeLE (z + 8 * i + 16) 8 v2).writeLE (z + 8 * i + 24) 8 v3).writeLE (z + 8 * i + 32) 8 v4).writeLE (z + 8 * i + 40) 8 v5) [(z, z + 8 * n)] := MemFrame.writeLE (MemFrame.writeLE hf2 _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)) _ (r := (z, z + 8 * n)) (by simp) (by omega) (by omega)
  refine segA3 s _ _ x y z i n m H3 _ _ _ _ cf3 of3 _ _ _ _ _ S3 hm64 hH3 hx6 hx7 hy6 hy7 (by omega) bz bx by' accz accx accy hf3 hpc3 h23 h33 hfl3
    h73 h83 h93 h103 hm3 (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx6]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry6]) hdx76 hdy76 (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [rx7]) (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [ry7]) hs3 ?_
  intro S4 v6 v7 H4 cf4 of4 pf4 af4 zf4 sf4 hpc4 h24 h34 hH4 hfl4 h64 h74 h84 h94 h104 he3 hm4 hs4
  exact hk S4 v0 v1 v2 v3 v4 v5 v6 v7 H1 H2 H3 H4 cf1 cf2 cf3 cf4 of1 of2 of3 of4 pf4 af4 zf4 sf4 hpc4 h24 h34 hH4 hfl4
    (by rw [h64, h63, h62, h61]) h74 h84 h94 h104 hm4 hs4 he0 he1 he2 he3

set_option exponentiation.threshold 1024 in
/-- the value of an ADX 8x block from its four pair equations, and the bound on the new carry word -/
theorem ablkval (v0 v1 v2 v3 v4 v5 v6 v7 x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 m W W1 W2 W3 W4 : Nat)
    (hy0 : y0 < 2 ^ 64) (hy1 : y1 < 2 ^ 64) (hy2 : y2 < 2 ^ 64) (hy3 : y3 < 2 ^ 64) (hy4 : y4 < 2 ^ 64)
    (hy5 : y5 < 2 ^ 64) (hy6 : y6 < 2 ^ 64) (hy7 : y7 < 2 ^ 64)
    (hx0 : x0 < 2 ^ 64) (hx1 : x1 < 2 ^ 64) (hx2 : x2 < 2 ^ 64) (hx3 : x3 < 2 ^ 64) (hx4 : x4 < 2 ^ 64)
    (hx5 : x5 < 2 ^ 64) (hx6 : x6 < 2 ^ 64) (hx7 : x7 < 2 ^ 64) (hm : m < 2 ^ 64) (hW : W < 2 ^ 64)
    (e0 : v0 % 2 ^ 64 + 2 ^ 64 * (v1 % 2 ^ 64) + 2 ^ 128 * W1 = (x0 + 2 ^ 64 * x1) + (m * y0 + 2 ^ 64 * (m * y1)) + W)
    (e1 : v2 % 2 ^ 64 + 2 ^ 64 * (v3 % 2 ^ 64) + 2 ^ 128 * W2 = (x2 + 2 ^ 64 * x3) + (m * y2 + 2 ^ 64 * (m * y3)) + W1)
    (e2 : v4 % 2 ^ 64 + 2 ^ 64 * (v5 % 2 ^ 64) + 2 ^ 128 * W3 = (x4 + 2 ^ 64 * x5) + (m * y4 + 2 ^ 64 * (m * y5)) + W2)
    (e3 : v6 % 2 ^ 64 + 2 ^ 64 * (v7 % 2 ^ 64) + 2 ^ 128 * W4 = (x6 + 2 ^ 64 * x7) + (m * y6 + 2 ^ 64 * (m * y7)) + W3) :
    (v0 % 2 ^ 64 + 2 ^ 64 * (v1 % 2 ^ 64) + 2 ^ 128 * (v2 % 2 ^ 64) + 2 ^ 192 * (v3 % 2 ^ 64) + 2 ^ 256 * (v4 % 2 ^ 64) +
      2 ^ 320 * (v5 % 2 ^ 64) + 2 ^ 384 * (v6 % 2 ^ 64) + 2 ^ 448 * (v7 % 2 ^ 64)) + 2 ^ 512 * W4 =
      (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 + 2 ^ 256 * x4 + 2 ^ 320 * x5 + 2 ^ 384 * x6 + 2 ^ 448 * x7) +
      (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 + 2 ^ 256 * y4 + 2 ^ 320 * y5 + 2 ^ 384 * y6 + 2 ^ 448 * y7) * m + W ∧
    W4 < 2 ^ 64 := by
  have hYm : (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 + 2 ^ 256 * y4 + 2 ^ 320 * y5 + 2 ^ 384 * y6 +
      2 ^ 448 * y7) * m ≤ (2 ^ 512 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hsum : (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 + 2 ^ 256 * y4 + 2 ^ 320 * y5 + 2 ^ 384 * y6 +
      2 ^ 448 * y7) * m = m * y0 + 2 ^ 64 * (m * y1) + 2 ^ 128 * (m * y2) + 2 ^ 192 * (m * y3) + 2 ^ 256 * (m * y4) +
      2 ^ 320 * (m * y5) + 2 ^ 384 * (m * y6) + 2 ^ 448 * (m * y7) := by
    rw [Nat.mul_comm]; simp only [Nat.mul_add, Nat.mul_left_comm m]
  rw [hsum] at hYm ⊢
  generalize m * y0 = p0 at *
  generalize m * y1 = p1 at *
  generalize m * y2 = p2 at *
  generalize m * y3 = p3 at *
  generalize m * y4 = p4 at *
  generalize m * y5 = p5 at *
  generalize m * y6 = p6 at *
  generalize m * y7 = p7 at *
  have := Nat.mod_lt v0 (show 0 < 2 ^ 64 by decide)
  constructor <;> omega

theorem ablk_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) :
    ∀ k (S : State) (i W : Nat), i + 8 * (k + 1) = n → W < 2 ^ 64 →
      S.rip = BitVec.ofNat 64 ahead8 → S.regs 6 = BitVec.ofNat 64 (k + 1) →
      S.regs 2 = BitVec.ofNat 64 m → S.regs 3 = BitVec.ofNat 64 W → S.regs 7 = 0#64 →
      S.regs 8 = BitVec.ofNat 64 (x + 8 * i) → S.regs 9 = BitVec.ofNat 64 (y + 8 * i) →
      S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      lv S.mem z i + 2 ^ (64 * i) * W = lv s.mem x i + lv s.mem y i * m + a →
      MemFrame s.mem S.mem [(z, z + 8 * i)] → Same64 s S →
      ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hm64 : m < 2 ^ 64 := hc.hm ▸ FvModexp.Asm.limb_lt _ _
  have bz := Arm64.Memory.accessible_bound _ hc.accz
  intro k
  induction k with
  | zero =>
    intro S i W hi hW hpc h6 h2 h3 h7 h8 h9 h10 hv hf hs
    have hn8 : n = i + 8 := by omega
    refine ablock s hc _ _ S i W (by omega) hW hpc h2 h3 h7 h8 h9 h10 hf hs ?_
    intro S4 v0 v1 v2 v3 v4 v5 v6 v7 H1 H2 H3 H4 cf1 cf2 cf3 cf4 of1 of2 of3 of4 pf af zf sf hpc4 h24 h34 hH4 hfl4 h64 h74
      h84 h94 h104 hm4 hs4 e0 e1 e2 e3
    obtain ⟨hval, hW4⟩ := ablkval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m W _ _ _ _ (FvModexp.Asm.limb_lt s.mem (y + 8 * i)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 8)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 16)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 24)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 32)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 40)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 48)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 56)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 8)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 16)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 24)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 32)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 40)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 48)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 56))
      hm64 hW e0 e1 e2 e3
    have hvb : lv S4.mem z (i + 8) + 2 ^ (64 * (i + 8)) * (H4 + cf4.toNat + of4.toNat) =
        lv s.mem x (i + 8) + lv s.mem y (i + 8) * m + a := by
      rw [hm4, lv_write8, lv_add8 s.mem x, lv_add8 s.mem y, pow_i8]
      exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv hval
    have hfz : MemFrame s.mem S4.mem [(z, z + 8 * (i + 8))] := by rw [hm4]; exact frame_ext8 hf _ _ _ _ _ _ _ _
    rw [hm4] at hvb hfz
    have hcw : (H4 + cf4.toNat) % 2 ^ 64 + of4.toNat < 2 ^ 64 ∧ ((H4 + cf4.toNat) % 2 ^ 64 + of4.toNat) = H4 + cf4.toNat + of4.toNat := by
      have := toNat_le_one cf4; have := toNat_le_one of4; constructor <;> omega
    subst hn8
    janus64_run until [entry + 0x253]
    exact fin_lem s hc _ 3 _ (Or.inr rfl) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff])
      (Or.inr ⟨rfl, rfl⟩) hW4 hvb hfz (by same64_tac hs4)
  | succ k ih =>
    intro S i W hi hW hpc h6 h2 h3 h7 h8 h9 h10 hv hf hs
    refine ablock s hc _ _ S i W (by omega) hW hpc h2 h3 h7 h8 h9 h10 hf hs ?_
    intro S4 v0 v1 v2 v3 v4 v5 v6 v7 H1 H2 H3 H4 cf1 cf2 cf3 cf4 of1 of2 of3 of4 pf af zf sf hpc4 h24 h34 hH4 hfl4 h64 h74
      h84 h94 h104 hm4 hs4 e0 e1 e2 e3
    obtain ⟨hval, hW4⟩ := ablkval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m W _ _ _ _ (FvModexp.Asm.limb_lt s.mem (y + 8 * i)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 8)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 16)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 24)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 32)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 40)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 48)) (FvModexp.Asm.limb_lt s.mem (y + 8 * i + 56)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 8)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 16)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 24)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 32)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 40)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 48)) (FvModexp.Asm.limb_lt s.mem (x + 8 * i + 56))
      hm64 hW e0 e1 e2 e3
    have hvb : lv S4.mem z (i + 8) + 2 ^ (64 * (i + 8)) * (H4 + cf4.toNat + of4.toNat) =
        lv s.mem x (i + 8) + lv s.mem y (i + 8) * m + a := by
      rw [hm4, lv_write8, lv_add8 s.mem x, lv_add8 s.mem y, pow_i8]
      exact addmul_step _ _ _ _ _ _ _ _ _ _ _ _ hv hval
    have hfz : MemFrame s.mem S4.mem [(z, z + 8 * (i + 8))] := by rw [hm4]; exact frame_ext8 hf _ _ _ _ _ _ _ _
    rw [hm4] at hvb hfz
    have hcw : (H4 + cf4.toNat) % 2 ^ 64 + of4.toNat < 2 ^ 64 ∧ ((H4 + cf4.toNat) % 2 ^ 64 + of4.toNat) = H4 + cf4.toNat + of4.toNat := by
      have := toNat_le_one cf4; have := toNat_le_one of4; constructor <;> omega
    rw [h6] at h64
    janus64_run until [entry + 0x176]
    refine ih _ (i + 8) _ (by omega) hW4 rfl ?r6 ?r2 ?r3 ?r7 ?r8 ?r9 ?r10 hvb hfz (by same64_tac hs4)
    case r6 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case r2 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h24
    case r3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
    case r7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h74
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem aone_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) :
    ∀ j (S : State) (i C : Nat), i + (j + 1) = n % 8 → C < 2 ^ 64 →
      S.rip = BitVec.ofNat 64 ahead1 → S.regs 11 = BitVec.ofNat 64 (j + 1) → S.regs 6 = BitVec.ofNat 64 (n / 8) →
      S.regs 2 = BitVec.ofNat 64 m → S.regs 3 = BitVec.ofNat 64 C → S.regs 7 = 0#64 →
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
    intro S i C hi hC hpc h11 h6 h2 h3 h7 h8 h9 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have hk := (am1 (m * s.mem.readLE (y + 8 * i) 8) C (s.mem.readLE (x + 8 * i) 8)
      (prod_le _ _ hm64 (FvModexp.Asm.limb_lt _ _)) hC (FvModexp.Asm.limb_lt _ _)).2
    rcases Nat.eq_zero_or_pos (n / 8) with hq | hq
    · have hn1 : n = i + 1 := by omega
      subst hn1
      janus64_run until [entry + 0x253]
      try simp only [rx0, ry0, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hC]
      exact fin_lem s hc _ 3 _ (Or.inr rfl) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rfl)
        (Or.inr ⟨rfl, rfl⟩) hk ((step1 s.mem S.mem z x y i m a C (m * s.mem.readLE (y + 8 * i) 8) hm64 hC (Nat.mul_comm _ _) hv _ (by unfold amr; omega)).1) (frame_ext hf _) (by same64_tac hs)
    · obtain ⟨q, hq'⟩ : ∃ q, n / 8 = q + 1 := ⟨n / 8 - 1, by omega⟩
      janus64_run until [entry + 0x176]
      try simp only [rx0, ry0, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hC]
      refine ablk_lem s hc q _ (i + 1) _ (by omega) hk rfl ?r6 ?r2 ?r3 ?r7 ?r8 ?r9 ?r10
        ((step1 s.mem S.mem z x y i m a C (m * s.mem.readLE (y + 8 * i) 8) hm64 hC (Nat.mul_comm _ _) hv _ (by unfold amr; omega)).1) (frame_ext hf _) (by same64_tac hs)
      case r6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rw [h6, hq']
      case r2 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h2
      case r3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rfl
      case r7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h7
      all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  | succ j ih =>
    intro S i C hi hC hpc h11 h6 h2 h3 h7 h8 h9 h10 hv hf hs
    have hs' := hs
    obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs'
    have rx0 := rd_frame (a := x + 8 * i) hf alx (by omega) (by omega) (by omega)
    have ry0 := rd_frame (a := y + 8 * i) hf aly (by omega) (by omega) (by omega)
    have hk := (am1 (m * s.mem.readLE (y + 8 * i) 8) C (s.mem.readLE (x + 8 * i) 8)
      (prod_le _ _ hm64 (FvModexp.Asm.limb_lt _ _)) hC (FvModexp.Asm.limb_lt _ _)).2
    janus64_run until [entry + 0x132]
    try simp only [rx0, ry0, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hC]
    refine ih _ (i + 1) _ (by omega) hk rfl ?s11 ?s6 ?s2 ?s3 ?s7 ?s8 ?s9 ?s10
      ((step1 s.mem S.mem z x y i m a C (m * s.mem.readLE (y + 8 * i) 8) hm64 hC (Nat.mul_comm _ _) hv _ (by unfold amr; omega)).1) (frame_ext hf _) (by same64_tac hs)
    case s11 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    case s6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h6
    case s2 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h2
    case s3 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; rfl
    case s7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; exact h7
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem lsr2' (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 2).toNat = n / 4 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem lsr3' (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3).toNat = n / 8 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem main_lem {z x y n m a : Nat} (s : State) (hc : Ctx s z x y n m a) (hpc : s.rip = BitVec.ofNat 64 entry) :
    ReachesRet program (retAddrOf s) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hr, hfb, hfacc, hadx, accz, accx, accy,
    alx, aly, azf⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have hm64 : m < 2 ^ 64 := h_rd_arg9 ▸ FvModexp.Asm.limb_lt _ _
  have ha64 : a < 2 ^ 64 := h_rd_arg10 ▸ FvModexp.Asm.limb_lt _ _
  have hn64 : n < 2 ^ 64 := by omega
  have hz0 : lv s.mem z 0 + 2 ^ (64 * 0) * a = lv s.mem x 0 + lv s.mem y 0 * m + a := by simp [lv_zero]
  have hs0 := Same64.refl s
  have h4 := lsr2' n hn64
  have h8 := lsr3' n hn64
  janus64_run until [head1, head4, fin, ahead1, ahead8, afin]
  · rw [h4] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    exact fin_lem s hc _ 6 a (Or.inl rfl) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]) (Or.inl ⟨rfl, rfl⟩) ha64 hz0 (frame_zero _ _) (by same64_tac hs0)
  · rw [h4] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 4 = q + 1 := ⟨n / 4 - 1, by omega⟩
    refine blk_lem s hc q _ 0 a (by omega) ha64 rfl ?r7 ?r3 ?r6 ?r8 ?r9 ?r10 hz0 (frame_zero _ _) (by same64_tac hs0)
    case r7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; rw [h4, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; try simp only [Nat.mul_zero, Nat.add_zero])
  · obtain ⟨j, hj⟩ : ∃ j, n % 4 = j + 1 := ⟨n % 4 - 1, by omega⟩
    refine one_lem s hc j _ 0 a (by omega) ha64 rfl ?t11 ?t7 ?t3 ?t6 ?t8 ?t9 ?t10 hz0 (frame_zero _ _) (by same64_tac hs0)
    case t11 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case t7 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; rw [h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; try simp only [Nat.mul_zero, Nat.add_zero])
  · rw [h8] at hbr
    have hn0 : n = 0 := by omega
    subst hn0
    exact fin_lem s hc _ 3 a (Or.inr rfl) (by simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]) (Or.inr ⟨rfl, rfl⟩) ha64 hz0 (frame_zero _ _) (by same64_tac hs0)
  · rw [h8] at hbr
    obtain ⟨q, hq⟩ : ∃ q, n / 8 = q + 1 := ⟨n / 8 - 1, by omega⟩
    refine ablk_lem s hc q _ 0 a (by omega) ha64 rfl ?u6 ?u2 ?u3 ?u7 ?u8 ?u9 ?u10 hz0 (frame_zero _ _) (by same64_tac hs0)
    case u6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; rw [h8, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; try simp only [Nat.mul_zero, Nat.add_zero])
  · obtain ⟨j, hj⟩ : ∃ j, n % 8 = j + 1 := ⟨n % 8 - 1, by omega⟩
    refine aone_lem s hc j _ 0 a (by omega) ha64 rfl ?w11 ?w6 ?w2 ?w3 ?w7 ?w8 ?w9 ?w10 hz0 (frame_zero _ _) (by same64_tac hs0)
    case w11 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; rw [and7_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case w6 => simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    all_goals (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; try simp only [Nat.mul_zero, Nat.add_zero])

/-- `addMulVVWW.abi0` as a callee, for both values of the `hasADX` flag -/
theorem addMulVVWW_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame; `adx` is the address of `math/big.hasADX` (readable, any value) -/
theorem ensures (z zl zc x xl xc y yl yc m a : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, y, yl, yc, m, a] 1
      (fun s => s.mem.accessible adxAddr 1 false = true ∧
        Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        Ptr s.mem y (8 * zl.toNat) false ∧
        (z.toNat = x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        (z.toNat = y.toNat ∨ Apart z.toNat (8 * zl.toNat) y.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 104)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat =
          (lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat * m.toNat + a.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 11 1 = [BitVec.ofNat 64
          ((lv s.mem x.toNat zl.toNat + lv s.mem y.toNat zl.toNat * m.toNat + a.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]) := by
  refine Ensures0.of_summary0 addMulVVWW_summary ?_ ?_
  · intro ret s hret hs ⟨hadx, ⟨hz1, hz2⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, alx, aly, azr⟩
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a9 := hs.arg (i := 9) (by simp)
    have a10 := hs.arg (i := 10) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6 a9 a10
    have hfa := hs.frame_accessible
    have hfb := hs.frame_bound
    simp only [List.length_cons, List.length_nil, Janus.Amd64.GoABI.regSP, Nat.reduceAdd, Nat.reduceMul,
      Nat.add_assoc] at hfa hfb
    have hr := hs.ret
    simp only [Amd64.Program.withExit, Janus.Amd64.GoABI.regSP] at hr
    unfold Pre
    rw [a0, a3, a6, a9, a10, a1]
    exact ⟨a0, a1, a3, a6, a9, a10, by rw [hr]; exact hret.user, by omega, hfa, hadx, hz1, hx1, hy1, alx, aly, azr⟩
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    have a9 := hs.arg (i := 9) (by simp)
    have a10 := hs.arg (i := 10) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6 a9 a10
    unfold Q at hq
    rw [a0, a3, a6, a9, a10, a1] at hq
    obtain ⟨q1, q3⟩ := hq
    have hZ := lv_lt s'.mem z.toNat zl.toNat
    have hP : 0 < 2 ^ (64 * zl.toNat) := Nat.two_pow_pos _
    refine ⟨?_, ?_, q3⟩
    · rw [← q1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hZ]
    · simp only [results0, wordsAt_succ, wordsAt_zero, Janus.Amd64.GoABI.regSP, Nat.reduceMul, Nat.reduceAdd]
      rw [show (s.regs 4).toNat + 8 + 88 = (s.regs 4).toNat + 96 by omega, ← q1, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt hZ, Nat.zero_add]

end FvModexp.Amd64.AddMulVVWWSum
