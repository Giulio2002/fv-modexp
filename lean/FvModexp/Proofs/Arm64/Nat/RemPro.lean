import FvModexp.Proofs.Arm64.Nat.RemDefs

set_option autoImplicit false

/-!
# `nat.rem` (arm64): the prologue — spills, `alias(z, u)` (excluded by `NoAlias`), the defer record, `k`, up to
`CALL (*stack).nat` (natdiv.go:506-510)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NatRem

theorem kq_eq (ul vl : BitVec 64) (h1 : ul.toNat ≤ 2 ^ 9) (h2 : vl.toNat ≤ 2 ^ 9) :
    (if (ul - vl + 1#64).toInt ≤ 1 then 1#64 else ul - vl + 1#64).toNat = kq ul.toNat vl.toNat % 2 ^ 64 := by
  have e : (ul - vl + 1#64).toNat = (ul.toNat + (2 ^ 64 - vl.toNat) + 1) % 2 ^ 64 := by
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [BitVec.toInt_eq_toNat_cond, e]
  simp only [kq]
  by_cases hA : 2 * ((ul.toNat + (2 ^ 64 - vl.toNat) + 1) % 2 ^ 64) < 2 ^ 64
  · rw [if_pos hA]; split <;> simp only [BitVec.toNat_ofNat, e] <;> omega
  · rw [if_neg hA]; split <;> simp only [BitVec.toNat_ofNat, e] <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- entry → `CALL (*stack).nat` -/
theorem pro (impl : List Segment) (s : State) (z zl zc st u ul uc v vl vc : BitVec 64)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (h0 : s.regs 0 = z) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = u)
    (h5 : s.regs 5 = ul) (h6 : s.regs 6 = uc) (h7 : s.regs 7 = v) (h8 : s.regs 8 = vl) (h9 : s.regs 9 = vc)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 41712 < s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb : 41712 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 41712) (41712 + 112) true = true)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 41712) (41712 + 112))
    (hstacc : s.mem.accessible st.toNat 24 false = true) (hst48 : st.toNat + 24 ≤ 2 ^ 48)
    (hsw : st.toNat + 24 ≤ s.sp.toNat - 41712 ∨ s.sp.toNat + 112 ≤ st.toNat)
    (hvu : vl.toNat ≤ 2 ^ 9) (hul : ul.toNat ≤ 2 ^ 9)
    (hna : NoAlias z.toNat zc.toNat u.toNat uc.toNat)
    (Q : State → Prop)
    (k : ∀ P, AtNat s P z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v.toNat vl.toNat vc.toNat →
      ReachesRet (LibRem.program.link impl) (s.regs 30) P Q) :
    ReachesRet (LibRem.program.link impl) (s.regs 30) s Q := by
  unfold Apart at hga
  janus_run until [callNat]
  all_goals first
    | (exfalso; exact hna (by omega) (by omega) (by simpa only [Nat.reducePow] using hbr.symm))
    | skip
  all_goals
    refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case qF => unfold fw; janus_frame
    case qR => simp only [Memory.regions_writeLE]
    all_goals try (janus_simp; done)
    all_goals (janus_simp; try omega)
    all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; try omega)
  all_goals exact kq_eq ul vl hul hvu

end FvModexp.Arm64.NatRem
