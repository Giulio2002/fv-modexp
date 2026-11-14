import FvModexp.Proofs.Amd64.Exp.ModInvSegC

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): one store into the frame inside a round (agent infra s58)

`cap_slot`: the stack header's capacity word survives a store into the frame window; `mid_st`: the round facts,
both operands' values / normalisation and the capacity survive a store into a local slot that is none of `Fw2`'s
(`mid_slot` + `cap_slot` + `norm_keep`). Used by every round segment for its spills and the return-address push.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem toNat_232 {sp : Nat} (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) :
    (BitVec.ofNat 64 (sp - 232)).toNat = sp - 224 - 8 := by
  rw [BitVec.toNat_ofNat]; omega

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

/-- a store into the frame window keeps the stack header's capacity word -/
theorem cap_slot (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (M : Memory) {a : Nat} (v : Nat)
    (h1 : (s.regs 4).toNat - (232 + kc) ≤ a) (h2 : a + 8 ≤ (s.regs 4).toNat) :
    stCap (M.writeLE a 8 v) st = stCap M st := by
  have hstw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw
  exact slot_other (by omega)

set_option maxRecDepth 20000 in
/-- the round facts, `z`'s and `zz`'s values / normalisation and the stack capacity survive a store into a local
slot (not one of `Fw2`'s) -/
theorem mid_st (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    {a : Nat} (v : Nat) (h1 : (s.regs 4).toNat - (232 + kc) ≤ a)
    (hm : a + 8 ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 8) :
    Mid R kc L s zp zc st xp xl xc n (M.writeLE a 8 v) L1 b1 p l c q ql qc ∧
      natVal (M.writeLE a 8 v) p l = natVal M p l ∧ natVal (M.writeLE a 8 v) q ql = natVal M q ql ∧
      (NatNorm M p l → NatNorm (M.writeLE a 8 v) p l) ∧ (NatNorm M q ql → NatNorm (M.writeLE a 8 v) q ql) ∧
      stCap (M.writeLE a 8 v) st = stCap M st := by
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  have hqlc : ql ≤ qc := hmid.2.2.2.2.2.2.1
  obtain ⟨m1, w1, w2⟩ := mid_slot hpre hmid v h1 hm
  exact ⟨m1, w1 l hlc, w2 ql hqlc, norm_keep w1 hlc, norm_keep w2 hqlc,
    cap_slot hpre M v h1 (by omega)⟩

end

end FvModexp.Amd64.ModInv
