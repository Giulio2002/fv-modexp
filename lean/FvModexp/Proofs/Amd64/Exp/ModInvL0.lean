import FvModexp.Proofs.Amd64.Exp.ModInvPostS

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): loop head `J2` → first call of a round (agent infra s58; twin of
`Arm64/Exp/ModInvL0`)

`+0x4ef` (`0x5eadaf`, nat.go:1326): `z` spilled to `0xb8 / 0xb0 / 0xd0(SP')` (`RSP - 40 / - 48 / - 16`: cap, len,
ptr); `CMPQ R12, BX; JB` (`i < numWords`, `BX = numWords`):
* loop body `+0x382` (`0x5eac42`): `i` → `0x98(SP')` (`RSP - 72`), `zz = zz.sqr(stk, z)` at `0x5eac60` (returns to
  `S1` loop, `0x5eac65`);
* exit `+0x510` (`0x5eadd0`): `zz = zz.sqr(stk, z)` at `0x5eade2` (returns to `S1` final, `0x5eade7`).
`runL` / `runF` are the straight-line runs (small context); `segL0` composes them with `mid_slot` and `callSqr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

/-- `z`'s spills at the loop head (`RSP' = sp - 224`) -/
@[reducible] def memZS (sp : Nat) (M : Memory) (p l c : Nat) : Memory :=
  ((M.writeLE (sp - 224 + 184) 8 c).writeLE (sp - 224 + 176) 8 l).writeLE (sp - 224 + 208) 8 p

theorem sp_m8 {sp : Nat} (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) :
    BitVec.ofNat 64 (sp - 224) - 8#64 = BitVec.ofNat 64 (sp - 232) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sqr_addr' : segAddr Extracted.program Q.NatSqr.fn = 6229984 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the loop branch (`i < numWords`): spills, `i` → `RSP - 72`, `nat.sqr`'s entry -/
theorem runL (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp p l c i nw q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hr : i < nw) (hi : i < 2 ^ 64) (hnw : nw < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x4ef)) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) 232 true = true)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h2 : S.regs 2 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (h12 : S.regs 12 = BitVec.ofNat 64 i) (h3 : S.regs 3 = BitVec.ofNat 64 nw)
    (h15 : S.regs 15 = BitVec.ofNat 64 q) (h13 : S.regs 13 = BitVec.ofNat 64 ql)
    (h11 : S.regs 11 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatSqr.fn) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = S.regs 7 → S'.regs 6 = BitVec.ofNat 64 p → S'.regs 8 = BitVec.ofNat 64 l →
      S'.regs 9 = BitVec.ofNat 64 c →
      S'.mem = ((memZS sp S.mem p l c).writeLE (sp - 224 + 152) 8 i).writeLE (sp - 224 - 8) 8 6204517 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  have hb : BitVec.ofNat 64 i < BitVec.ofNat 64 nw := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hnw]; exact hr
  rw [sqr_addr'] at K
  janus64_run [hb] until [6229984]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the exit branch (`numWords ≤ i`): spills, `nat.sqr`'s entry -/
theorem runF (impl : List Amd64.Segment) (ra : W64) (Qp : State → Prop) (sp p l c i nw q ql qc : Nat)
    (hsp : 232 ≤ sp) (hsp2 : sp ≤ 2 ^ 48) (hr : ¬ i < nw) (hi : i < 2 ^ 64) (hnw : nw < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x4ef)) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 224))
    (hacc : S.mem.accessible (sp - 232) 232 true = true)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h2 : S.regs 2 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (h12 : S.regs 12 = BitVec.ofNat 64 i) (h3 : S.regs 3 = BitVec.ofNat 64 nw)
    (h15 : S.regs 15 = BitVec.ofNat 64 q) (h13 : S.regs 13 = BitVec.ofNat 64 ql)
    (h11 : S.regs 11 = BitVec.ofNat 64 qc)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatSqr.fn) →
      S'.regs 4 = BitVec.ofNat 64 (sp - 232) → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 0 = BitVec.ofNat 64 q → S'.regs 3 = BitVec.ofNat 64 ql → S'.regs 1 = BitVec.ofNat 64 qc →
      S'.regs 7 = S.regs 7 → S'.regs 6 = BitVec.ofNat 64 p → S'.regs 8 = BitVec.ofNat 64 l →
      S'.regs 9 = BitVec.ofNat 64 c →
      S'.mem = (memZS sp S.mem p l c).writeLE (sp - 224 - 8) 8 6204903 →
      ReachesRet (LibW.program.link impl) ra S' Qp) :
    ReachesRet (LibW.program.link impl) ra S Qp := by
  have hb : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 nw := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hnw]; exact hr
  rw [sqr_addr'] at K
  janus64_run [hb] until [6229984]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | (janus64_simp; exact sp_m8 hsp hsp2)

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
/-- the round facts after the loop head's stores (`z`'s spills, `i` (loop only) and the return address) -/
theorem mid_L0 (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) (i r : Nat)
    (hi : i < 2 ^ 64) (hr : r < 2 ^ 64) :
    let sp := (s.regs 4).toNat
    let ML := ((memZS sp M p l c).writeLE (sp - 224 + 152) 8 i).writeLE (sp - 224 - 8) 8 r
    let MF := (memZS sp M p l c).writeLE (sp - 224 - 8) 8 r
    (Mid R kc L s zp zc st xp xl xc n ML L1 b1 p l c q ql qc ∧ ZS s ML p l c ∧ natVal ML p l = natVal M p l ∧
      ML.readLE (sp - 72) 8 = i ∧ ML.readLE (sp - 224 - 8) 8 = r ∧ stCap ML st = stCap M st) ∧
    (Mid R kc L s zp zc st xp xl xc n MF L1 b1 p l c q ql qc ∧ ZS s MF p l c ∧ natVal MF p l = natVal M p l ∧
      MF.readLE (sp - 224 - 8) 8 = r ∧ stCap MF st = stCap M st) := by
  intro sp ML MF
  have hK : 232 + kc ≤ sp := sp_K hpre
  have hp : p < 2 ^ 64 := hmid.2.2.1.2.1
  have hc : c < 2 ^ 40 := hmid.2.2.1.1
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  obtain ⟨m1, w1, -⟩ := mid_slot hpre hmid (a := sp - 224 + 184) c (by omega) (by omega)
  obtain ⟨m2, w2, -⟩ := mid_slot hpre m1 (a := sp - 224 + 176) l (by omega) (by omega)
  obtain ⟨m3, w3, -⟩ := mid_slot hpre m2 (a := sp - 224 + 208) p (by omega) (by omega)
  obtain ⟨m4, w4, -⟩ := mid_slot hpre m3 (a := sp - 224 + 152) i (by omega) (by omega)
  obtain ⟨m5, w5, -⟩ := mid_slot hpre m4 (a := sp - 224 - 8) r (by omega) (by omega)
  obtain ⟨m5', w5', -⟩ := mid_slot hpre m3 (a := sp - 224 - 8) r (by omega) (by omega)
  have v3 : natVal (memZS sp M p l c) p l = natVal M p l := by
    simp only [natVal, memZS]; rw [w3 l hlc, w2 l hlc, w1 l hlc]
  have z3 : ZS s (memZS sp M p l c) p l c := by
    simp only [ZS, memZS]
    refine ⟨?_, ?_, ?_⟩
    · rw [show sp - 16 = sp - 224 + 208 by omega, slot_self hp]
    · rw [slot_other (by omega), show sp - 48 = sp - 224 + 176 by omega, slot_self (by omega)]
    · rw [slot_other (by omega), slot_other (by omega), show sp - 40 = sp - 224 + 184 by omega,
        slot_self (by omega)]
  have c3 : stCap (memZS sp M p l c) st = stCap M st := by
    simp only [memZS]
    rw [cap_slot hpre _ _ (by omega) (by omega), cap_slot hpre _ _ (by omega) (by omega),
      cap_slot hpre _ _ (by omega) (by omega)]
  refine ⟨⟨m5, ?_, ?_, ?_, slot_self hr, ?_⟩, ⟨m5', ?_, ?_, slot_self hr, ?_⟩⟩
  · obtain ⟨z1, z2, z3⟩ := z3
    exact ⟨(slot_other (by omega)).trans ((slot_other (by omega)).trans z1),
      (slot_other (by omega)).trans ((slot_other (by omega)).trans z2),
      (slot_other (by omega)).trans ((slot_other (by omega)).trans z3)⟩
  · simp only [natVal]; rw [w5 l hlc, w4 l hlc]; exact v3
  · rw [slot_other (by omega), show sp - 72 = sp - 224 + 152 by omega, slot_self hi]
  · rw [cap_slot hpre _ _ (by omega) (by omega), cap_slot hpre _ _ (by omega) (by omega)]; exact c3
  · obtain ⟨z1, z2, z3⟩ := z3
    exact ⟨(slot_other (by omega)).trans z1, (slot_other (by omega)).trans z2, (slot_other (by omega)).trans z3⟩
  · simp only [natVal]; rw [w5' l hlc]; exact v3
  · rw [cap_slot hpre _ _ (by omega) (by omega)]; exact c3

/-- a loop round's budget fits (`i = 2^j < numWords`: round `j ≤ log2 numWords`) -/
theorem bud_jL {j : Nat} (hc : cost sqrC mulC xl n ≤ b) (hj1 : 1 ≤ j) (hr : 2 ^ j < NW n) :
    spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (2 ^ j) ≤ b := by
  have hNW0 : NW n ≠ 0 := by have := Nat.two_pow_pos j; omega
  have hjl : j ≤ Nat.log2 (NW n) := (Nat.le_log2 hNW0).2 (Nat.le_of_lt hr)
  have hm := sumR_mono sqrC mulC xl n hjl
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [sumR_succ] at hm
  simp only [spent, cost, Nat.add_sub_cancel] at hc ⊢
  omega

/-- the final round's budget fits (`2^(j-1) < numWords`) -/
theorem bud_jF {j : Nat} (hc : cost sqrC mulC xl n ≤ b) (hjn : 2 ^ (j - 1) < NW n)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a') :
    spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (NW n) ≤ b := by
  have hNW0 : NW n ≠ 0 := by have := Nat.two_pow_pos (j - 1); omega
  have hjl : j - 1 ≤ Nat.log2 (NW n) := (Nat.le_log2 hNW0).2 (Nat.le_of_lt hjn)
  have hm := sumR_mono sqrC mulC xl n hjl
  have hs := hsm _ _ (zB_le hjn)
  simp only [spent, cost, roundCost] at hc ⊢
  omega

end

end FvModexp.Amd64.ModInv
