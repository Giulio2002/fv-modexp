import FvModexp.Proofs.Amd64.NatQ.RemDefs

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): the prologue — stack check, spills, `alias(z, u)` (excluded by `NoAlias`), the defer
record, `k`, up to `CALL (*stack).nat` (natdiv.go:505-510); twin of Arm64/NatQ/RemPro.lean
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

open FvModexp.Amd64.NHyp (NoAlias)

theorem kq_eq (ul : BitVec 64) (vl : Nat) (h1 : ul.toNat ≤ 2 ^ 9) (h2 : vl ≤ 2 ^ 9) :
    (if 1 < (ul - BitVec.ofNat 64 vl + 1#64).toInt then ul - BitVec.ofNat 64 vl + 1#64 else 1#64).toNat =
      kq ul.toNat vl % 2 ^ 64 := by
  have e : (ul - BitVec.ofNat 64 vl + 1#64).toNat = (ul.toNat + (2 ^ 64 - vl) + 1) % 2 ^ 64 := by
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [BitVec.toInt_eq_toNat_cond, e]
  simp only [kq]
  by_cases hA : 2 * ((ul.toNat + (2 ^ 64 - vl) + 1) % 2 ^ 64) < 2 ^ 64
  · rw [if_pos hA]; split <;> simp only [BitVec.toNat_ofNat, e] <;> omega
  · rw [if_neg hA]; split <;> simp only [BitVec.toNat_ofNat, e] <;> omega

theorem alias_eq {z zc u uc : Nat} (hz : z < 2 ^ 64) (hzc : zc < 2 ^ 64) (hu : u < 2 ^ 64) (huc : uc < 2 ^ 64)
    (h0 : ¬zc = 0) (h1 : ¬uc = 0)
    (h : (18446744073709551616 - (18446744073709551608 + (z + zc * 8 % 18446744073709551616) % 18446744073709551616) %
            18446744073709551616 +
          (18446744073709551608 + (u + uc * 8 % 18446744073709551616) % 18446744073709551616) %
            18446744073709551616) % 18446744073709551616 = 0) :
    (z + 8 * (zc - 1)) % 2 ^ 64 = (u + 8 * (uc - 1)) % 2 ^ 64 := by
  omega

/-- a hidden hypothesis (kept out of the executor's omega calls) -/
structure Hide (P : Prop) : Prop where
  h : P

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → `CALL (*stack).nat` -/
theorem pro (impl : List Amd64.Segment) (R : RtInv) (L : List (Nat × Nat)) (s : State)
    (z zl zc st u ul uc : BitVec 64) (vl : Nat)
    (hpc : s.rip = BitVec.ofNat 64 base)
    (h0 : s.regs 0 = z) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = u)
    (h8 : s.regs 8 = ul) (h9 : s.regs 9 = uc)
    (hce : CallEnv R L s 41720 112)
    (hvlS : s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl)
    (hstacc8 : s.mem.accessible (st.toNat + 8) 8 false = true) (hst48 : st.toNat + 24 ≤ 2 ^ 48)
    (hsw : st.toNat + 24 ≤ (s.regs 4).toNat - 41720 ∨ (s.regs 4).toNat + 112 ≤ st.toNat)
    (hvl : vl ≤ 2 ^ 9) (hul : ul.toNat ≤ 2 ^ 9)
    (hna : NoAlias z.toNat zc.toNat u.toNat uc.toNat)
    (Q : State → Prop)
    (k : ∀ P, AtNat s P z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat vl →
      ReachesRet (LibRem.program.link impl) (retAddrOf s) P Q) :
    ReachesRet (LibRem.program.link impl) (retAddrOf s) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  clear hLs hout hgr
  have hnaH : Hide (NoAlias z.toNat zc.toNat u.toNat uc.toNat) := ⟨hna⟩
  clear hna
  janus64_run [hvlS, hstacc8] until [callNat]
  all_goals first
    | (exfalso; exact hnaH.h (by omega) (by omega) (alias_eq z.isLt zc.isLt u.isLt uc.isLt (by janus_assumption) (by janus_assumption) hbr))
    | skip
  all_goals
    refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    case qF => unfold fw; janus_frame
    case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
    all_goals try (janus64_simp; done)
    all_goals (janus64_simp; try omega)
    all_goals try (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; try omega)
  all_goals exact kq_eq ul vl hul hvl
