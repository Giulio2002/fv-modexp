import FvModexp.Proofs.Arm64.Nat.DivDefs

/-!
# `nat.div` (arm64): the segment-boundary relations (shared by the path modules)

`SP = s.sp` (entry), `SP' = SP - 240`. `AtW`: after `divW` returned (`fn + 0x6c`); `AtC`: after `nat.cmp` returned
(`fn + 0x140`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatDiv

/-- `divW`'s return site -/
abbrev retW : Nat := 0x1b926c
/-- `nat.cmp`'s return site -/
abbrev retC : Nat := 0x1b9340
/-- `divLarge`'s return site -/
abbrev retL : Nat := 0x1b94d4
/-- `nat.cmp`'s entry -/
abbrev cmpE : Nat := 1782608

/-- the frame ranges written before the first call: saved `X29`/`X30`, locals, spills -/
@[reducible] def proW (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 248, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 112)]

/-- the facts after `divW` returned (`len v = 1`): `q = (q, ql, qc)` with `U / V`, `X3 = U % V` -/
structure AtW (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc z2 z2c u ul v vl : Nat) (s : State)
    (q ql qc : Nat) (L' : List (Nat × Nat)) (b' : Nat) (T : State) : Prop where
  pc : T.pc = BitVec.ofNat 64 retW
  sp : T.sp = s.sp - 240#64
  r28 : T.regs 28 = s.regs 28
  r29 : T.regs 29 = s.sp - 248#64
  r18 : T.regs 18 = s.regs 18
  r0 : T.regs 0 = BitVec.ofNat 64 q
  r1 : T.regs 1 = BitVec.ofNat 64 ql
  r2 : T.regs 2 = BitVec.ofNat 64 qc
  r3 : (T.regs 3).toNat = natVal s.mem u ul % natVal s.mem v vl
  hq : ExpHyp.NatOF R L L' T.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl)
  ext : LiveExt R L L'
  bud : b - makeCost ul ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' T.mem)
  mf : MemFrame s.mem T.mem (R.rt ++ winA s 41504 112 ++ ar zp zc)
  lf : LiveFrame s.mem T.mem L (ar zp zc)
  reg : T.mem.regions = s.mem.regions
  lr : T.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : T.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  s5 : T.mem.readLE (s.sp.toNat + 40) 8 = z2
  s7 : T.mem.readLE (s.sp.toNat + 56) 8 = z2c

/-- the facts after `nat.cmp` returned (`len v ≥ 2`): only the window written, `X0` = the comparison -/
structure AtC (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s S : State) : Prop where
  pc : S.pc = BitVec.ofNat 64 retC
  sp : S.sp = s.sp - 240#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 248#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = CmpSum.cmpRes ul vl (s.mem.readLE u (8 * ul)) (s.mem.readLE v (8 * vl))
  mf : MemFrame s.mem S.mem (winA s 41504 112)
  reg : S.mem.regions = s.mem.regions
  lr : S.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : S.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  s1 : S.mem.readLE (s.sp.toNat + 8) 8 = zp
  s2 : S.mem.readLE (s.sp.toNat + 16) 8 = zl
  s3 : S.mem.readLE (s.sp.toNat + 24) 8 = zc
  s4 : S.mem.readLE (s.sp.toNat + 32) 8 = st
  s5 : S.mem.readLE (s.sp.toNat + 40) 8 = z2
  s6 : S.mem.readLE (s.sp.toNat + 48) 8 = z2l
  s7 : S.mem.readLE (s.sp.toNat + 56) 8 = z2c
  s8 : S.mem.readLE (s.sp.toNat + 64) 8 = u
  s9 : S.mem.readLE (s.sp.toNat + 72) 8 = ul
  s10 : S.mem.readLE (s.sp.toNat + 80) 8 = uc
  s11 : S.mem.readLE (s.sp.toNat + 88) 8 = v
  s12 : S.mem.readLE (s.sp.toNat + 96) 8 = vl
  s13 : S.mem.readLE (s.sp.toNat + 104) 8 = vc

/-- `z2.set(u)`'s copy point (`fn + 0x1c4`, `u < v`): `r`'s array `(p, c)` chosen (`z2` reused or fresh), `q = z[:0]`
stored -/
abbrev joinS : Nat := 0x1b93c4

structure AtS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc z2 z2c u ul : Nat) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (S : State) : Prop where
  pc : S.pc = BitVec.ofNat 64 joinS
  sp : S.sp = s.sp - 240#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 248#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 ul
  r1 : S.regs 1 = BitVec.ofNat 64 ul
  r2 : S.regs 2 = BitVec.ofNat 64 p
  r6 : S.regs 6 = BitVec.ofNat 64 c
  arr : (p = z2 ∧ c = z2c ∧ ul ≤ z2c) ∨
    (z2c < ul ∧ ul ≤ c ∧ c ≤ ul + 4 ∧ p % 8 = 0 ∧ p + 8 * c ≤ 2 ^ 48 ∧ InRanges p (8 * c) R.rt ∧
      ApartAll p (8 * c) L ∧ InRanges p (8 * c) L' ∧ S.mem.accessible p (8 * c) true = true)
  ext : LiveExt R L L'
  bud : b - makeCost ul ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' S.mem)
  mf : MemFrame s.mem S.mem (R.rt ++ winA s 41504 112)
  lf : LiveFrame s.mem S.mem L []
  reg : S.mem.regions = s.mem.regions
  lr : S.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : S.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  q0 : S.mem.readLE (s.sp.toNat - 56) 8 = zp
  q1 : S.mem.readLE (s.sp.toNat - 48) 8 = 0
  q2 : S.mem.readLE (s.sp.toNat - 40) 8 = zc
  s8 : S.mem.readLE (s.sp.toNat + 64) 8 = u

/-- `divLarge`'s window bounds in the entry's terms (standalone: `omega` chokes on nested subtractions in big contexts) -/
theorem spX {s X : State} (hsp : X.sp = s.sp - 240#64) (h : 41504 ≤ s.sp.toNat) :
    X.sp.toNat - 41264 = s.sp.toNat - 41504 ∧ X.sp.toNat - 8 = s.sp.toNat - 248 ∧ X.sp.toNat + 8 = s.sp.toNat - 232 ∧
      X.sp.toNat + 112 = s.sp.toNat - 128 ∧ X.sp.toNat = s.sp.toNat - 240 := by
  have : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  omega

/-! ## The comparison `u.cmp(v)` for normalised nats -/

theorem natVal_ge1 (m : Memory) (p n : Nat) (hn : 1 ≤ n) (ht : m.readLE (p + 8 * (n - 1)) 8 ≠ 0) :
    2 ^ (64 * (n - 1)) ≤ natVal m p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht ⊢
  rw [natVal_succ]
  have : 1 ≤ m.readLE (p + 8 * k) 8 := Nat.pos_of_ne_zero ht
  calc 2 ^ (64 * k) = 2 ^ (64 * k) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (64 * k) * m.readLE (p + 8 * k) 8 := Nat.mul_le_mul_left _ this
    _ ≤ _ := Nat.le_add_left _ _

/-- a normalised nat with more limbs is larger -/
theorem len_le_of_lt {m : Memory} {u ul v vl : Nat} (hu : NatNorm m u ul) (h : natVal m u ul < natVal m v vl) :
    ul ≤ vl := by
  rcases hu with h0 | ht
  · omega
  · refine Nat.le_of_not_lt fun hc => ?_
    have h1 := natVal_ge1 m u ul (by omega) ht
    have h2 := natVal_lt m v vl
    have h3 : 2 ^ (64 * vl) ≤ 2 ^ (64 * (ul - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem cmp_lt {m : Memory} {u ul v vl : Nat} (hu : NatNorm m u ul) (h : natVal m u ul < natVal m v vl) :
    CmpSum.cmpRes ul vl (m.readLE u (8 * ul)) (m.readLE v (8 * vl)) = 18446744073709551615#64 := by
  have hl := len_le_of_lt hu h
  unfold CmpSum.cmpRes
  by_cases h1 : ul < vl
  · rw [if_pos h1]
  · have e : ul = vl := by omega
    subst e
    have h' : m.readLE u (8 * ul) < m.readLE v (8 * ul) := h
    simp [h']

theorem cmp_ge {m : Memory} {u ul v vl : Nat} (hv : NatNorm m v vl) (h : natVal m v vl ≤ natVal m u ul) :
    ∃ c, c ≤ 1 ∧ CmpSum.cmpRes ul vl (m.readLE u (8 * ul)) (m.readLE v (8 * vl)) = BitVec.ofNat 64 c := by
  have hl : vl ≤ ul := by
    rcases Nat.lt_or_ge (natVal m v vl) (natVal m u ul) with h1 | h1
    · exact len_le_of_lt hv h1
    · rcases hv with h0 | ht
      · omega
      · refine Nat.le_of_not_lt fun hc => ?_
        have h2 := natVal_ge1 m v vl (by omega) ht
        have h3 := natVal_lt m u ul
        have h4 : 2 ^ (64 * ul) ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
  unfold CmpSum.cmpRes
  rw [if_neg (by omega)]
  by_cases h1 : vl < ul
  · exact ⟨1, by omega, by rw [if_pos h1]⟩
  · have e : ul = vl := by omega
    subst e
    have h' : m.readLE v (8 * ul) ≤ m.readLE u (8 * ul) := h
    rw [if_neg h1, if_neg (by omega)]
    by_cases h2 : m.readLE v (8 * ul) < m.readLE u (8 * ul)
    · exact ⟨1, by omega, by rw [if_pos h2]⟩
    · exact ⟨0, by omega, by rw [if_neg h2]⟩

end FvModexp.Arm64.NatDiv
