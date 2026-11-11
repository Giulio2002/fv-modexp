import FvModexp.Proofs.Arm64.Exp.SubMod2NSeg2

/-!
# `nat.subMod2N` (arm64): `J3` → `J4`, the loop `for uint(len(z))*_W < n { z = append(z, 0) }` (nat.go:1748)

`cap z = zc ≥ ⌈n/64⌉` (`z` reused by `z.sub(y, x)`), so `append` never calls `growslice`: each iteration stores a
zero limb at `z[len]` and increments `len`, until `len = ⌈n/64⌉`. (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

theorem fw_zstore {s : State} {M : Memory} {zp zl zc yp n : Nat} (h : Fw s M zp zl zc yp n) {a v : Nat}
    (hz : zp ≤ a) (hz2 : a + 8 ≤ zp + 8 * zc)
    (hzw : zp + 8 * zc ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zp) (hs : 4608 ≤ s.sp.toNat) :
    Fw s (M.writeLE a 8 v) zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ b, s.sp.toNat - 152 ≤ b → b + 8 ≤ s.sp.toNat + 88 → (M.writeLE a 8 v).readLE b 8 = M.readLE b 8 :=
    fun b h1 h2 => Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  exact ⟨(r _ (by omega) (by omega)).trans f1, (r _ (by omega) (by omega)).trans f2, (r _ (by omega) (by omega)).trans f3,
    (r _ (by omega) (by omega)).trans f4, (r _ (by omega) (by omega)).trans f5, (r _ (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega)).trans f7⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- one test of the append loop (at `+0x260`) -/
theorem appIter (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k4 : J4 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (S : State) (l : Nat) (L3 : List (Nat × Nat)) (b3 : Nat)
    (hpc : S.pc = BitVec.ofNat 64 (1805584 + 0x260)) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 l) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hfw : Fw s S.mem zp zl zc yp n) (hrt : Rt R b L s zp zc n 3 S.mem L3 b3)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hv : natVal S.mem zp l = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) (hl : l ≤ W n)
    (KL : ∀ S' : State, l + 1 ≤ W n → S'.pc = BitVec.ofNat 64 (1805584 + 0x260) →
      S'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) → S'.regs 28 = s.regs 28 → S'.regs 18 = s.regs 18 →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 (l + 1) → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 9 = BitVec.ofNat 64 n → Fw s S'.mem zp zl zc yp n → Rt R b L s zp zc n 3 S'.mem L3 b3 →
      natVal S'.mem zp (l + 1) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n →
      Goal impl R b L zp zl zc yp yl n s S') :
    Goal impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, hzlive, hzw, -⟩ :=
    id hpre
  simp only [W] at hW hl
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hb' ha hw
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hacc : S.mem.accessible zp (8 * zc) true = true := (hrt.2.2.2.2.2.2 (by omega)).2.2.1
  rw [show (1805584 + 0x260 : Nat) = 1806192 from rfl] at hpc
  have hsh : (BitVec.ofNat 64 l <<< 6).toNat = 64 * l := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  unfold Goal
  by_cases hc : n ≤ 64 * l
  · have hlW : l = (n + 63) / 64 := by omega
    subst hlW
    janus_run [hc, hsh] until [1806236]
    refine k4 _ L3 b3 hpre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrt hlt hv
    all_goals janus_simp
  · have e : (BitVec.ofNat 64 l + 1#64 - 1#64) = BitVec.ofNat 64 l := BitVec.add_sub_cancel _ _
    have hcap : l + 1 ≤ zc := by omega
    janus_run [hc, hsh, e] until [1806192]
    refine KL _ (by simp only [W]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try janus_simp
    · apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    · exact fw_zstore hfw (by omega) (by omega) hzw (by omega)
    · exact rt_zstore hpre hrt (by omega) (by omega)
    · rw [show zp + l * 8 = zp + 8 * l by omega, natVal_store_top _ _ _ _ (by decide), hv]; omega

theorem app (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k4 : J4 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s) :
    ∀ (k : Nat) (S : State) (l : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - l = k →
    S.pc = BitVec.ofNat 64 (1805584 + 0x260) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 l → S.regs 2 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 n → Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem zp l = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → l ≤ W n →
    Goal impl R b L zp zl zc yp yl n s S := by
  intro k
  induction k with
  | zero =>
    intro S l L3 b3 hk hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlt hv hl
    exact appIter impl k4 hpre S l L3 b3 hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlt hv hl
      fun _ h => absurd h (by omega)
  | succ k ih =>
    intro S l L3 b3 hk hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlt hv hl
    exact appIter impl k4 hpre S l L3 b3 hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlt hv hl
      fun S' hl1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 => ih S' (l + 1) L3 b3 (by omega) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hlt a11 hl1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s4a (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k4 : J4 impl R b L op zp zl zc yp yl yc n s) : J3 impl R b L op zp zl zc yp yl yc n s := by
  intro S l3 L3 b3 hpre hpc hsp h28 h18 h0 h1 h2 hfw hrt hlt hv hn hl3
  rw [show (1805584 + 0x21c : Nat) = 1806124 from rfl] at hpc
  have hs4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hacc : S.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hpre.1.2.1.2.2.2
  have ha := hpre.1.2.1.2.2.1
  have hal : s.sp.toNat % 16 = 0 := hpre.1.2.1.1
  simp only [A] at ha
  have r80 : S.mem.readLE (s.sp.toNat - 144 + 224) 8 = n := by
    rw [show s.sp.toNat - 144 + 224 = s.sp.toNat + 80 by omega]; exact hfw.2.2.2.2.2.2
  unfold Goal
  janus_run [r80] until [1806192]
  refine app impl k4 hpre _ _ l3 L3 b3 rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrt hlt hv hl3
  all_goals janus_simp

end FvModexp.Arm64.SubMod2N
