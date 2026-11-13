import FvModexp.Proofs.Arm64.Exp.ModInvJoin

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): helpers shared by the round segments (agent infra)

`mid_frame`: the round facts survive stack-slot stores (inside `winA`), the owned arrays' words unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- a normalised nat below `2^(64k)` has at most `k` words -/
theorem len_le {m : Memory} {p l k : Nat} (hn : NatNorm m p l) (hv : natVal m p l < 2 ^ (64 * k)) : l ≤ k := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · omega
  · have := SubMod2N.natVal_lower m p l hn h0
    have h2 : 2 ^ (64 * (l - 1)) < 2 ^ (64 * k) := Nat.lt_of_le_of_lt this hv
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega

/-- `makeCost` is monotone above `1` (`makeCap 1 = 1`, `makeCap 0 = 4`) -/
theorem makeCost_mono {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

/-- `LSL $6` of `i = 2^j` as Janus spells it (rotate + masks) -/
theorem lsl6_pow (j : Nat) (hj : j < 12) :
    (BitVec.ofNat 64 (2 ^ j)).rotateRight 58 &&& 18446744073709551552#64 &&& 18446744073709551615#64 =
      BitVec.ofNat 64 (2 ^ j * 64) := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 20000 in
/-- a stack-slot store is inside `winA` -/
theorem frame_slot {s : State} {kc : Nat} (m : Memory) {a : Nat} (v : Nat) (h1 : s.sp.toNat - (240 + kc) ≤ a)
    (h2 : a + 8 ≤ s.sp.toNat - 8) : MemFrame m (m.writeLE a 8 v) (winA s (K kc) A) := by
  show MemFrame m _ [(s.sp.toNat - (240 + kc), s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]
  exact (MemFrame.refl m _).writeLE_inRanges v ⟨(s.sp.toNat - (240 + kc), s.sp.toNat - 8), List.mem_cons_self .., h1, h2⟩

set_option maxRecDepth 20000 in
/-- the spills `Fw2` survive a store into a local slot that is none of them -/
theorem fw2_slot {s : State} {m : Memory} {st xp xl xc n : Nat} (h : Fw2 s m st xp xl xc n) {a : Nat} (v : Nat)
    (hsp : 248 ≤ s.sp.toNat) (hlo : s.sp.toNat - 232 ≤ a)
    (hm : a + 8 ≤ s.sp.toNat - 112 ∨ s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 32 ≤ a)
    (hhi : a + 8 ≤ s.sp.toNat + 32) : Fw2 s (m.writeLE a 8 v) st xp xl xc n := by
  obtain ⟨⟨f1, f2⟩, f3, f4, f5, f6, f7, f8, f9⟩ := h
  have r : ∀ x, x + 8 ≤ a ∨ a + 8 ≤ x → (m.writeLE a 8 v).readLE x 8 = m.readLE x 8 := fun x hx =>
    Memory.readLE_writeLE_of_disjoint _ _ hx
  exact ⟨⟨(r _ (by omega)).trans f1, (r _ (by omega)).trans f2⟩, (r _ (by omega)).trans f3, (r _ (by omega)).trans f4,
    (r _ (by omega)).trans f5, (r _ (by omega)).trans f6, (r _ (by omega)).trans f7, (r _ (by omega)).trans f8,
    (r _ (by omega)).trans f9⟩

/-- the spill slots `[SP - 152, SP + 72)` unchanged -/
@[reducible] def SlotsKept (s : State) (M M' : Memory) : Prop :=
  ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 72 → M'.readLE a 8 = M.readLE a 8

theorem zs_keep {s : State} {M M' : Memory} {p l c : Nat} (h : SlotsKept s M M') (hsp : 240 ≤ s.sp.toNat)
    (hz : ZS s M p l c) : ZS s M' p l c :=
  ⟨(h _ (by omega) (by omega)).trans hz.1, (h _ (by omega) (by omega)).trans hz.2.1,
    (h _ (by omega) (by omega)).trans hz.2.2⟩

theorem qs_keep {s : State} {M M' : Memory} {q ql qc : Nat} (h : SlotsKept s M M') (hsp : 240 ≤ s.sp.toNat)
    (hz : QS s M q ql qc) : QS s M' q ql qc :=
  ⟨(h _ (by omega) (by omega)).trans hz.1, (h _ (by omega) (by omega)).trans hz.2.1,
    (h _ (by omega) (by omega)).trans hz.2.2⟩

theorem slot_keep {s : State} {M M' : Memory} (h : SlotsKept s M M') (hsp : 240 ≤ s.sp.toNat) {d v : Nat}
    (hd : 8 ≤ d) (hd' : d ≤ 152) (hv : M.readLE (s.sp.toNat - d) 8 = v) : M'.readLE (s.sp.toNat - d) 8 = v :=
  (h _ (by omega) (by omega)).trans hv

/-- one budget step: the callee spent at most `m` -/
theorem bud_step {b S p b1 mc m b' r r' : Nat} (hb : b - S - p + r ≤ b1) (h' : b1 - (mc + r) + r' ≤ b')
    (hm : mc ≤ m) : b - S - (p + m) + r' ≤ b' := by omega

/-- one budget step through a callee that keeps the stack capacity (plain cost, same reserve) -/
theorem bud_stepP {b S rc p b1 mc m b' r : Nat} (hb : b - S - p + r ≤ b1) (hbud : S + rc ≤ b) (hp : p + m ≤ rc)
    (h' : b1 - mc ≤ b') (hm : mc ≤ m) : b - S - (p + m) + r ≤ b' := by omega

/-- a callee's charge fits the budget left in the round -/
theorem bud_ok {b S rc p b1 m mc r : Nat} (hb : b - S - p + r ≤ b1) (hbud : S + rc ≤ b) (hp : p + m ≤ rc)
    (hm : mc ≤ m) : mc + r ≤ b1 := by omega

/-- `bud_ok` without the reserve (a plain callee's charge) -/
theorem bud_okP {b S rc p b1 m mc r : Nat} (hb : b - S - p + r ≤ b1) (hbud : S + rc ≤ b) (hp : p + m ≤ rc)
    (hm : mc ≤ m) : mc ≤ b1 := by omega

/-- `z`'s slots survive a store below them -/
theorem zs_store {s : State} {M : Memory} {p l c a : Nat} (v : Nat) (hz : ZS s M p l c) (ha : a + 8 ≤ s.sp.toNat - 56)
    (hsp : 56 ≤ s.sp.toNat) : ZS s (M.writeLE a 8 v) p l c := by
  obtain ⟨z1, z2, z3⟩ := hz
  exact ⟨(Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans z1,
    (Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans z2, (Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans z3⟩

/-- a product of a `≤ x`-word and a `≤ y`-word value has at most `x + y` words -/
theorem len_le_mul {m : Memory} {p l a c x y : Nat} (hn : NatNorm m p l) (hv : natVal m p l = a * c)
    (ha : a < 2 ^ (64 * x)) (hc : c < 2 ^ (64 * y)) : l ≤ x + y := by
  refine len_le hn ?_
  rw [hv, show 64 * (x + y) = 64 * x + 64 * y by omega, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt ha hc

/-- `z` has a word: its value is odd -/
theorem len_pos {X Zv j : Nat} {m : Memory} {p l : Nat} (hc : X * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hv : natVal m p l = Zv) : 0 < l := by
  have ho := Exp.odd_of_inv (Nat.le_trans (by decide) (Nat.mul_le_mul_right 32 (Nat.one_le_two_pow (n := j)))) hc
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0
    have := natVal_lt m p 0
    simp only [Nat.mul_zero, Nat.pow_zero] at this
    omega
  · exact h0

theorem bud_ok0 {b S rc b1 m mc r : Nat} (hb : b - S + r ≤ b1) (hbud : S + rc ≤ b) (hp : m ≤ rc) (hm : mc ≤ m) :
    mc + r ≤ b1 := by omega

theorem bud_step0 {b S b1 mc m b' r r' : Nat} (hb : b - S + r ≤ b1) (h' : b1 - (mc + r) + r' ≤ b') (hm : mc ≤ m) :
    b - S - m + r' ≤ b' := by omega

/-- `NatNorm` from equal prefixes -/
theorem norm_keep {M M' : Memory} {o oc l : Nat} (h : ∀ k, k ≤ oc → M'.readLE o (8 * k) = M.readLE o (8 * k))
    (hl : l ≤ oc) (hn : NatNorm M o l) : NatNorm M' o l := by
  rcases hn with hn | hn
  · exact Or.inl hn
  rcases Nat.eq_zero_or_pos l with h0 | hl0
  · exact Or.inl h0
  refine Or.inr ?_
  have e := natVal_succ M o (l - 1)
  have e' := natVal_succ M' o (l - 1)
  rw [Nat.sub_add_cancel hl0] at e e'
  have a1 : natVal M' o l = natVal M o l := h l hl
  have a2 : natVal M' o (l - 1) = natVal M o (l - 1) := h (l - 1) (by omega)
  have hp := Nat.two_pow_pos (64 * (l - 1))
  have : 2 ^ (64 * (l - 1)) * M'.readLE (o + 8 * (l - 1)) 8 = 2 ^ (64 * (l - 1)) * M.readLE (o + 8 * (l - 1)) 8 := by
    omega
  rw [Nat.eq_of_mul_eq_mul_left hp this]; exact hn

/-- final round: `E = n`, `Kx = numWords` -/
@[reducible] def eF (n _j : Nat) : Nat := n
@[reducible] def kF (n _j : Nat) : Nat := NW n

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

/-- an owned array's words through stack-slot stores -/
theorem own_read {L1 : List (Nat × Nat)} {M M' : Memory} {p c : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    (hF : MemFrame M M' (winA s (K kc) A)) {k : Nat} (hk : k ≤ c) : M'.readLE p (8 * k) = M.readLE p (8 * k) := by
  refine hF.readLE _ _ ?_
  have := h.2.2.2.2.1
  simp only [win, winA, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega

theorem own_norm {L1 : List (Nat × Nat)} {M M' : Memory} {p c : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    (hF : MemFrame M M' (winA s (K kc) A)) {k : Nat} (hk : k ≤ c) (hn : NatNorm M p k) : NatNorm M' p k := by
  refine SubMod2N.natNorm_frame hF ?_ hn
  have := h.2.2.2.2.1
  simp only [win, winA, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega

set_option maxRecDepth 20000 in
/-- the round facts survive stack-slot stores -/
theorem mid_frame (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hF : MemFrame M M' (winA s (K kc) A)) (hreg : M'.regions = M.regions) (hfw : Fw2 s M' st xp xl xc n) :
    Mid R kc L s zp zc st xp xl xc n M' L1 b1 p l c q ql qc := by
  obtain ⟨-, hrt, hz, hzz, r⟩ := hmid
  have hstw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw
  have hst : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    hF.readLE _ _ (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
  have e0 : stW M' st = stW M st := by have := hst 0 (by omega); simpa only [Nat.add_zero] using this
  have e1 : stLen M' st = stLen M st := hst 8 (by omega)
  have e2 : stCap M' st = stCap M st := hst 16 (by omega)
  exact ⟨hfw, rtM_stk hpre hrt hF hreg, own_mono hz (LiveExt.refl R L1) hF.accessible e0 e1 e2,
    own_mono hzz (LiveExt.refl R L1) hF.accessible e0 e1 e2, r⟩

end
end FvModexp.Arm64.ModInv

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- the memory after `zz`'s spills to `SP - 24 / - 128 / - 120` -/
@[reducible] def memZZ (s : State) (M : Memory) (q ql qc : Nat) : Memory :=
  ((M.writeLE (s.sp.toNat - 240 + 216) 8 q).writeLE (s.sp.toNat - 240 + 112) 8 ql).writeLE
    (s.sp.toNat - 240 + 120) 8 qc

set_option maxRecDepth 20000 in
/-- `zz`'s spills: the round facts survive, `zz`'s slots hold it, other slots and the owned arrays unchanged -/
theorem store_zz {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    (hq : q < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64) (hkc : 4608 ≤ kc) :
    Mid R kc L s zp zc st xp xl xc n (memZZ s M q ql qc) L1 b1 p l c q ql qc ∧ QS s (memZZ s M q ql qc) q ql qc ∧
      (∀ a, (a + 8 ≤ s.sp.toNat - 128 ∨ s.sp.toNat - 112 ≤ a ∧ a + 8 ≤ s.sp.toNat - 24 ∨ s.sp.toNat - 16 ≤ a) →
        (memZZ s M q ql qc).readLE a 8 = M.readLE a 8) ∧
      (∀ k, k ≤ c → (memZZ s M q ql qc).readLE p (8 * k) = M.readLE p (8 * k)) ∧
      (∀ k, k ≤ qc → (memZZ s M q ql qc).readLE q (8 * k) = M.readLE q (8 * k)) := by
  have hK := sp_K hpre
  have hsp0 : 248 ≤ s.sp.toNat := by omega
  have F1 := frame_slot (s := s) (kc := kc) M q (a := s.sp.toNat - 240 + 216) (by omega) (by omega)
  have F2 := frame_slot (s := s) (kc := kc) (M.writeLE (s.sp.toNat - 240 + 216) 8 q) ql
    (a := s.sp.toNat - 240 + 112) (by omega) (by omega)
  have F3 := frame_slot (s := s) (kc := kc) ((M.writeLE (s.sp.toNat - 240 + 216) 8 q).writeLE
    (s.sp.toNat - 240 + 112) 8 ql) qc (a := s.sp.toNat - 240 + 120) (by omega) (by omega)
  have w1 := fw2_slot (a := s.sp.toNat - 240 + 216) hmid.1 q hsp0 (by omega) (by omega) (by omega)
  have w2 := fw2_slot (a := s.sp.toNat - 240 + 112) w1 ql hsp0 (by omega) (by omega) (by omega)
  have w3 := fw2_slot (a := s.sp.toNat - 240 + 120) w2 qc hsp0 (by omega) (by omega) (by omega)
  have m1 := mid_frame hpre hmid F1 (Memory.regions_writeLE _ _ _ _) w1
  have m2 := mid_frame hpre m1 F2 (Memory.regions_writeLE _ _ _ _) w2
  have m3 := mid_frame hpre m2 F3 (Memory.regions_writeLE _ _ _ _) w3
  have hlc := hmid.2.2.2.2.2.1
  refine ⟨m3, ⟨?_, ?_, ?_⟩, fun a ha => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [memZZ]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 24 = s.sp.toNat - 240 + 216 by omega, Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hq]
  · simp only [memZZ]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 128 = s.sp.toNat - 240 + 112 by omega, Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hql]
  · simp only [memZZ]
    rw [show s.sp.toNat - 120 = s.sp.toNat - 240 + 120 by omega, Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hqc]
  · simp only [memZZ]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · exact ((own_read m2.2.2.1 F3 hk).trans (own_read m1.2.2.1 F2 hk)).trans (own_read hmid.2.2.1 F1 hk)
  · exact ((own_read m2.2.2.2.1 F3 hk).trans (own_read m1.2.2.2.1 F2 hk)).trans (own_read hmid.2.2.2.1 F1 hk)

end FvModexp.Arm64.ModInv

namespace FvModexp.Arm64.ModInv

/-- one loop round's value, in the joins' terms (`x[:k]` as a prefix of the normalised `x`) -/
theorem round_step {m : Memory} {xp xl Zv j : Nat} (hx : NatNorm m xp xl)
    (hc : natVal m xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)) :
    natVal m xp xl * Exp.subMod2N (Zv * 2) (Zv * Zv % 2 ^ (2 ^ j * 64) * natVal m xp (min (2 ^ j) xl) %
      2 ^ (2 ^ j * 64)) (2 ^ j * 64) % 2 ^ (2 ^ (j + 1) * 32) = 1 % 2 ^ (2 ^ (j + 1) * 32) := by
  have e : natVal m xp (min (2 ^ j) xl) = natVal m xp xl % Exp.B ^ min (2 ^ j) (Exp.nlen (natVal m xp xl)) := by
    rw [SubMod2N.norm_nlen m xp xl hx]; exact Exp.natVal_prefix m xp _ xl (Nat.min_le_right _ _)
  rw [e]; exact Exp.round_inv _ _ _ hc

/-- the final round's value -/
theorem final_step {m : Memory} {xp xl Zv j n : Nat} (hx : NatNorm m xp xl) (hodd : natVal m xp xl % 2 = 1)
    (hn : 64 < n) (hj : NW n ≤ 2 ^ j) (hc : natVal m xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)) :
    Exp.subMod2N (Zv * 2) (Zv * Zv % 2 ^ n * natVal m xp (min (NW n) xl) % 2 ^ n) n = val (natVal m xp xl) n := by
  have e : natVal m xp (min (NW n) xl) = natVal m xp xl % Exp.B ^ min ((n + 63) / 64) (Exp.nlen (natVal m xp xl)) := by
    rw [SubMod2N.norm_nlen m xp xl hx]; exact Exp.natVal_prefix m xp _ xl (Nat.min_le_right _ _)
  rw [e]; exact Exp.final_val _ _ _ _ hodd hn hj hc

theorem spent_succ (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j : Nat) (hj : 1 ≤ j) :
    spent sqrC mulC xl n (j + 1) = spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (2 ^ j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [spent, Nat.add_sub_cancel, sumR_succ]
  omega

/-- (s45) the stack header lies outside the frame window -/
theorem st_out {R : RtInv} {kc H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) :
    st + 24 ≤ s.sp.toNat - (240 + kc) ∨ s.sp.toNat + 72 ≤ st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hstw, -, -⟩, -⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true, K, A] at hstw
  omega

/-- (s45) a frame-slot store keeps the stack capacity (for `stkR_congr`) -/
theorem cap_slot {R : RtInv} {kc H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (m : Memory) {a : Nat} (v : Nat)
    (h1 : s.sp.toNat - (240 + kc) ≤ a) (h2 : a + 8 ≤ s.sp.toNat + 72) :
    stCap (m.writeLE a 8 v) st = stCap m st := by
  have := st_out hpre
  exact Memory.readLE_writeLE_of_disjoint (m := m) v (by omega)

end FvModexp.Arm64.ModInv
