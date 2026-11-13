import FvModexp.Proofs.Amd64.Nat.DivDefs

set_option autoImplicit false

/-!
# `nat.div` (amd64): the segment-boundary relations (shared by the path modules)

`SP = s.regs 4` (entry), `SP' = SP - 232` (`PUSHQ BP; SUBQ $0xe0, SP`). `AtC`: after `nat.cmp` returned
(`fn + 0x1cf`). Register spills: `z` at `SP + 56 … + 72`, `stk` at `SP + 80`, `z2` at `SP + 88 … + 104`; the stack
arguments `u` at `SP + 8 … + 24`, `v` at `SP + 32 … + 48`. Port of `Arm64/Nat/DivRel.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatDiv

/-- `nat.cmp`'s return site (`fn + 0x1cf`) -/
abbrev retC : Nat := 0x5ee0ef
/-- `nat.cmp`'s entry -/
abbrev cmpE : Nat := 6184128

/-- the facts after `nat.cmp` returned (`len v ≥ 2`): only the window written, `RAX` = the comparison -/
structure AtC (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 retC
  sp : S.regs 4 = s.regs 4 - 232#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  r0 : S.regs 0 = CmpSum.cmpRes ul vl (FvModexp.Asm.lv s.mem u ul) (FvModexp.Asm.lv s.mem v vl)
  mf : MemFrame s.mem S.mem (win s 41512 112)
  reg : S.mem.regions = s.mem.regions
  ra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  s1 : S.mem.readLE ((s.regs 4).toNat + 56) 8 = zp
  s2 : S.mem.readLE ((s.regs 4).toNat + 64) 8 = zl
  s3 : S.mem.readLE ((s.regs 4).toNat + 72) 8 = zc
  s4 : S.mem.readLE ((s.regs 4).toNat + 80) 8 = st
  s5 : S.mem.readLE ((s.regs 4).toNat + 88) 8 = z2
  s6 : S.mem.readLE ((s.regs 4).toNat + 96) 8 = z2l
  s7 : S.mem.readLE ((s.regs 4).toNat + 104) 8 = z2c
  s8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = u
  s9 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ul
  s10 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = uc
  s11 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = v
  s12 : S.mem.readLE ((s.regs 4).toNat + 40) 8 = vl
  s13 : S.mem.readLE ((s.regs 4).toNat + 48) 8 = vc
  q0 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = 0

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
    CmpSum.cmpRes ul vl (FvModexp.Asm.lv m u ul) (FvModexp.Asm.lv m v vl) = 18446744073709551615#64 := by
  have hl := len_le_of_lt hu h
  unfold CmpSum.cmpRes
  by_cases h1 : ul < vl
  · rw [if_pos h1]
  · have e : ul = vl := by omega
    subst e
    have h' : FvModexp.Asm.lv m u ul < FvModexp.Asm.lv m v ul := h
    simp [h']

theorem cmp_ge {m : Memory} {u ul v vl : Nat} (hv : NatNorm m v vl) (h : natVal m v vl ≤ natVal m u ul) :
    ∃ c, c ≤ 1 ∧ CmpSum.cmpRes ul vl (FvModexp.Asm.lv m u ul) (FvModexp.Asm.lv m v vl) = BitVec.ofNat 64 c := by
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
    have h' : FvModexp.Asm.lv m v ul ≤ FvModexp.Asm.lv m u ul := h
    rw [if_neg h1, if_neg (by omega)]
    by_cases h2 : FvModexp.Asm.lv m v ul < FvModexp.Asm.lv m u ul
    · exact ⟨1, by omega, by rw [if_pos h2]⟩
    · exact ⟨0, by omega, by rw [if_neg h2]⟩

end FvModexp.Amd64.NatDiv
