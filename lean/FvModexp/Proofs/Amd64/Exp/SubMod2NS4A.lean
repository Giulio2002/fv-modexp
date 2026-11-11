import FvModexp.Proofs.Amd64.Exp.SubMod2NSeg2

/-!
# `nat.subMod2N` (amd64): `J3` → `J4`, the loop `for uint(len(z))*_W < n { z = append(z, 0) }` (nat.go:1748)

`cap z = zc ≥ ⌈n/64⌉`, so `append` never calls `growslice`: each iteration stores a zero limb at `z[len]` and increments
`len`, until `len = ⌈n/64⌉`. Loop head `+0x300` (`RAX = zp`, `RBX = len`, `RCX = zc`, `RDX = n`). (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

theorem fw_zstore {s : State} {M : Memory} {zp zl zc yp n : Nat} (h : Fw s M zp zl zc yp n) {a v : Nat}
    (hz : zp ≤ a) (hz2 : a + 8 ≤ zp + 8 * zc)
    (hzw : zp + 8 * zc ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ zp) (hs : 4576 ≤ (s.regs 4).toNat) :
    Fw s (M.writeLE a 8 v) zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ b, (s.regs 4).toNat - 8 ≤ b → b + 8 ≤ (s.regs 4).toNat + 88 → (M.writeLE a 8 v).readLE b 8 = M.readLE b 8 :=
    fun b h1 h2 => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  exact ⟨(r _ (by omega) (by omega)).trans f1, (r _ (by omega) (by omega)).trans f2, (r _ (by omega) (by omega)).trans f3,
    (r _ (by omega) (by omega)).trans f4, (r _ (by omega) (by omega)).trans f5, (r _ (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega)).trans f7⟩

theorem natVal_store_top' (m : Memory) (p k v a : Nat) (ha : a = p + 8 * k) (hv : v < 2 ^ 64) :
    natVal (m.writeLE a 8 v) p (k + 1) = natVal m p k + 2 ^ (64 * k) * v := by
  subst ha; exact natVal_store_top m p k v hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- one test of the append loop (at `+0x300`) -/
theorem appIter (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k4 : J4 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    (S : State) (l : Nat) (L3 : List (Nat × Nat)) (b3 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 6216608) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128))
    (hab : Abi s S)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (hfw : Fw s S.mem zp zl zc yp n) (hrt : Rt R b L s zp zc n 3 S.mem L3 b3)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hv : natVal S.mem zp l = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) (hl : l ≤ W n)
    (KL : ∀ S' : State, l + 1 ≤ W n → S'.rip = BitVec.ofNat 64 6216608 →
      S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S' →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 3 = BitVec.ofNat 64 (l + 1) → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 2 = BitVec.ofNat 64 n → Fw s S'.mem zp zl zc yp n → Rt R b L s zp zc n 3 S'.mem L3 b3 →
      natVal S'.mem zp (l + 1) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n →
      Goal impl R b L zp zl zc yp yl n s S') :
    Goal impl R b L zp zl zc yp yl n s S := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, -, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, hzlive, hzw, -⟩ :=
    id hpre
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  simp only [W] at hW hl
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hb' ha hw
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hacc : S.mem.accessible zp (8 * zc) true = true := (hrt.2.2.2.2.2.2 (by omega)).2.2.1
  have hsh : (BitVec.ofNat 64 l <<< 6).toNat = 64 * l := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  unfold Goal
  by_cases hc : n ≤ 64 * l
  · have hlW : l = (n + 63) / 64 := by omega
    subst hlW
    janus64_run [hc, hsh] until [6216656]
    refine k4 _ L3 b3 hpre ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ hfw hrt hlt hv
    all_goals first | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | janus64_simp
  · have hcap : l + 1 ≤ zc := by omega
    janus64_run [hc, hsh, hcap] until [6216608]
    refine KL _ (by simp only [W]; omega) ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp; exact hfs
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · exact fw_zstore hfw (by omega) (by omega) hzw (by omega)
    · exact rt_zstore hpre hrt (by omega) (by omega)
    · refine (natVal_store_top' _ _ _ _ _ ?_ (by decide)).trans ?_
      · omega
      · rw [hv]; omega

theorem app (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k4 : J4 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s) :
    ∀ (k : Nat) (S : State) (l : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - l = k →
    S.rip = BitVec.ofNat 64 6216608 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 3 = BitVec.ofNat 64 l → S.regs 1 = BitVec.ofNat 64 zc →
    S.regs 2 = BitVec.ofNat 64 n → Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem zp l = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → l ≤ W n →
    Goal impl R b L zp zl zc yp yl n s S := by
  intro k
  induction k with
  | zero =>
    intro S l L3 b3 hk hpc hsp hab h0 h3 h1 h2 hfw hrt hlt hv hl
    exact appIter impl k4 hpre S l L3 b3 hpc hsp hab h0 h3 h1 h2 hfw hrt hlt hv hl
      fun _ h => absurd h (by omega)
  | succ k ih =>
    intro S l L3 b3 hk hpc hsp hab h0 h3 h1 h2 hfw hrt hlt hv hl
    exact appIter impl k4 hpre S l L3 b3 hpc hsp hab h0 h3 h1 h2 hfw hrt hlt hv hl
      fun S' hl1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 => ih S' (l + 1) L3 b3 (by omega) a1 a2 a3 a4 a5 a6 a7 a8 a9 hlt a10 hl1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s4a (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k4 : J4 impl R b L op zp zl zc yp yl yc n s) : J3 impl R b L op zp zl zc yp yl yc n s := by
  intro S l3 L3 b3 hpre hpc hsp hab h0 h3 h1 hfw hrt hlt hv hn hl3
  have hs4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have r8 : S.mem.readLE ((s.regs 4).toNat - 128 + 136) 8 = n := by
    rw [show (s.regs 4).toNat - 128 + 136 = (s.regs 4).toNat + 8 by omega]; exact hfw.2.2.2.2.2.2
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hpre.1.2.1.2.2
  unfold Goal
  janus64_run [r8] until [6216608]
  refine app impl k4 hpre _ _ l3 L3 b3 rfl ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ hfw hrt hlt hv hl3
  all_goals first | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | janus64_simp

end FvModexp.Amd64.SubMod2N
