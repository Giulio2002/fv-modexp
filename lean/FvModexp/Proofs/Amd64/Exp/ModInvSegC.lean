import FvModexp.Proofs.Amd64.Exp.ModInvJoin
import FvModexp.Proofs.Amd64.Exp.ModInvSt
import FvModexp.Proofs.Amd64.Exp.SubMod2NSeg

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): shared round lemmas (agent infra s57; twin of `Arm64/Exp/ModInvSegC`)

Pure lemmas every round segment uses: lengths (`len_le`, `len_le_mul`, `len_pos`), budget steps (`bud_*`), the round
values (`round_step`, `final_step`, `spent_succ`), and the frame-slot stores: a store into a local slot
(`RSP - (232 + kc) ≤ a`, `a + 8 ≤ RSP - 8`, not one of `Fw2`'s) keeps `Mid` (`mid_slot`), the owned arrays' words
(`own_read1`) and the slots at or above `RSP - 144` other than `a` (`SlotsKept`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

/-- a normalised nat below `2^(64k)` has at most `k` words -/
theorem len_le {m : Memory} {p l k : Nat} (hn : NatNorm m p l) (hv : natVal m p l < 2 ^ (64 * k)) : l ≤ k := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · omega
  · have := FvModexp.SubMod2N.natVal_lower m p l hn h0
    have h2 : 2 ^ (64 * (l - 1)) < 2 ^ (64 * k) := Nat.lt_of_le_of_lt this hv
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega

/-- `makeCost` is monotone above `1` (`makeCap 1 = 1`, `makeCap 0 = 4`) -/
theorem makeCost_mono {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

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

/-- one loop round's value, in the joins' terms (`x[:k]` as a prefix of the normalised `x`) -/
theorem round_step {m : Memory} {xp xl Zv j : Nat} (hx : NatNorm m xp xl)
    (hc : natVal m xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)) :
    natVal m xp xl * Exp.subMod2N (Zv * 2) (Zv * Zv % 2 ^ (2 ^ j * 64) * natVal m xp (min (2 ^ j) xl) %
      2 ^ (2 ^ j * 64)) (2 ^ j * 64) % 2 ^ (2 ^ (j + 1) * 32) = 1 % 2 ^ (2 ^ (j + 1) * 32) := by
  have e : natVal m xp (min (2 ^ j) xl) = natVal m xp xl % Exp.B ^ min (2 ^ j) (Exp.nlen (natVal m xp xl)) := by
    rw [FvModexp.SubMod2N.norm_nlen m xp xl hx]; exact Exp.natVal_prefix m xp _ xl (Nat.min_le_right _ _)
  rw [e]; exact Exp.round_inv _ _ _ hc

/-- the final round's value -/
theorem final_step {m : Memory} {xp xl Zv j n : Nat} (hx : NatNorm m xp xl) (hodd : natVal m xp xl % 2 = 1)
    (hn : 64 < n) (hj : NW n ≤ 2 ^ j) (hc : natVal m xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32)) :
    Exp.subMod2N (Zv * 2) (Zv * Zv % 2 ^ n * natVal m xp (min (NW n) xl) % 2 ^ n) n = val (natVal m xp xl) n := by
  have e : natVal m xp (min (NW n) xl) = natVal m xp xl % Exp.B ^ min ((n + 63) / 64) (Exp.nlen (natVal m xp xl)) := by
    rw [FvModexp.SubMod2N.norm_nlen m xp xl hx]; exact Exp.natVal_prefix m xp _ xl (Nat.min_le_right _ _)
  rw [e]; exact Exp.final_val _ _ _ _ hodd hn hj hc

theorem spent_succ (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (xl n j : Nat) (hj : 1 ≤ j) :
    spent sqrC mulC xl n (j + 1) = spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (2 ^ j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [spent, Nat.add_sub_cancel, sumR_succ]
  omega

/-! ## Slot stores -/

/-- the slots `[RSP - 144, RSP + 72)` unchanged -/
@[reducible] def SlotsKept (s : State) (M M' : Memory) : Prop :=
  ∀ a, (s.regs 4).toNat - 144 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 → M'.readLE a 8 = M.readLE a 8

theorem zs_keep {s : State} {M M' : Memory} {p l c : Nat} (h : SlotsKept s M M') (hsp : 232 ≤ (s.regs 4).toNat)
    (hz : ZS s M p l c) : ZS s M' p l c :=
  ⟨(h _ (by omega) (by omega)).trans hz.1, (h _ (by omega) (by omega)).trans hz.2.1,
    (h _ (by omega) (by omega)).trans hz.2.2⟩

theorem qs_keep {s : State} {M M' : Memory} {q ql qc : Nat} (h : SlotsKept s M M') (hsp : 232 ≤ (s.regs 4).toNat)
    (hz : QS s M q ql qc) : QS s M' q ql qc :=
  ⟨(h _ (by omega) (by omega)).trans hz.1, (h _ (by omega) (by omega)).trans hz.2.1,
    (h _ (by omega) (by omega)).trans hz.2.2⟩

theorem slot_keep {s : State} {M M' : Memory} (h : SlotsKept s M M') (hsp : 232 ≤ (s.regs 4).toNat) {d v : Nat}
    (hd : 8 ≤ d) (hd' : d ≤ 144) (hv : M.readLE ((s.regs 4).toNat - d) 8 = v) :
    M'.readLE ((s.regs 4).toNat - d) 8 = v :=
  (h _ (by omega) (by omega)).trans hv

/-- a store keeps every slot it does not overlap -/
theorem slot_other {M : Memory} {a v x : Nat} (h : x + 8 ≤ a ∨ a + 8 ≤ x) : (M.writeLE a 8 v).readLE x 8 = M.readLE x 8 :=
  Arm64.Memory.readLE_writeLE_of_disjoint _ _ h

theorem slot_self {M : Memory} {a v : Nat} (hv : v < 2 ^ 64) : (M.writeLE a 8 v).readLE a 8 = v := by
  rw [Arm64.Memory.readLE_writeLE_self, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hv]

/-- `z`'s slots survive a store that misses them -/
theorem zs_store {s : State} {M : Memory} {p l c a : Nat} (v : Nat) (hz : ZS s M p l c)
    (ha : a + 8 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 32 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 16 ∨
      (s.regs 4).toNat - 8 ≤ a) (hsp : 48 ≤ (s.regs 4).toNat) : ZS s (M.writeLE a 8 v) p l c := by
  obtain ⟨z1, z2, z3⟩ := hz
  exact ⟨(slot_other (by omega)).trans z1, (slot_other (by omega)).trans z2, (slot_other (by omega)).trans z3⟩

/-- `zz`'s slots survive a store that misses them -/
theorem qs_store {s : State} {M : Memory} {q ql qc a : Nat} (v : Nat) (hz : QS s M q ql qc)
    (ha : a + 8 ≤ (s.regs 4).toNat - 120 ∨ (s.regs 4).toNat - 104 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 24 ∨
      (s.regs 4).toNat - 16 ≤ a) (hsp : 120 ≤ (s.regs 4).toNat) : QS s (M.writeLE a 8 v) q ql qc := by
  obtain ⟨z1, z2, z3⟩ := hz
  exact ⟨(slot_other (by omega)).trans z1, (slot_other (by omega)).trans z2, (slot_other (by omega)).trans z3⟩

/-- the spills `Fw2` survive a store into a local slot that is none of them -/
theorem fw2_slot {s : State} {m : Memory} {st xp xl xc n : Nat} (h : Fw2 s m st xp xl xc n) {a : Nat} (v : Nat)
    (hm : a + 8 ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 8)
    (hsp : 232 ≤ (s.regs 4).toNat) : Fw2 s (m.writeLE a 8 v) st xp xl xc n := by
  obtain ⟨⟨f1, f2⟩, f3, f4, f5, f6, f7, f9⟩ := h
  exact ⟨⟨(slot_other (by omega)).trans f1, (slot_other (by omega)).trans f2⟩, (slot_other (by omega)).trans f3,
    (slot_other (by omega)).trans f4, (slot_other (by omega)).trans f5, (slot_other (by omega)).trans f6,
    (slot_other (by omega)).trans f7, (slot_other (by omega)).trans f9⟩

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the runtime facts survive a store into the window -/
theorem rtM_slot (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {a v : Nat} (h1 : (s.regs 4).toNat - (232 + kc) ≤ a)
    (h2 : a + 8 ≤ (s.regs 4).toNat + 72) : RtM R kc L s zp zc st (M.writeLE a 8 v) L1 b1 := by
  obtain ⟨⟨-, -, -, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hstw, -⟩, -⟩ := hpre
  simp only [K, A] at hout
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨r0, F0, LF0, LE0, inv0, stk0, len0, arr0, ain0⟩ := hrt
  have hst : Outside st 24 [(a, a + 8)] := by simp only [outside_cons, outside_nil, and_true]; omega
  have hF1 : MemFrame M (M.writeLE a 8 v) [(a, a + 8)] :=
    (MemFrame.refl M _).writeLE_inRanges _ ⟨(a, a + 8), by simp, by simp only; omega, by simp only; omega⟩
  obtain ⟨hstk, e0, e1, e2⟩ := stkOK_frame stk0 hF1 hst (LiveExt.refl R L1)
  have hrt' : Outside a 8 R.rt := hout.of_sub (by omega) (by omega)
  refine ⟨by rw [Arm64.Memory.regions_writeLE]; exact r0, ?_, ?_, LE0, inv_store_held inv0 (Or.inr hrt'), hstk,
    e1.trans len0, by rw [e0, e2]; exact arr0, ArrIn.congr ain0 e0 e2 fun _ h => h⟩
  · refine F0.writeLE_inRanges v ⟨((s.regs 4).toNat - (232 + kc), (s.regs 4).toNat + 72), ?_, by simp only; omega,
      by simp only; omega⟩
    simp only [win, K, A, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  · refine LF0.writeLE v (Janus.Contracts.outside_of_forall fun r hr => ?_)
    have := hLs r hr
    simp only [win, K, A, outside_cons, outside_nil, and_true] at this
    omega

/-- an owned array's words through a store into the window -/
theorem own_read1 {L1 : List (Nat × Nat)} {M : Memory} {p c : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    {a v : Nat} (h1 : (s.regs 4).toNat - (232 + kc) ≤ a) (h2 : a + 8 ≤ (s.regs 4).toNat + 72) {k : Nat} (hk : k ≤ c) :
    (M.writeLE a 8 v).readLE p (8 * k) = M.readLE p (8 * k) := by
  have := h.2.2.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at this
  exact Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)

set_option maxRecDepth 20000 in
/-- the round facts survive a store into a local slot (not one of `Fw2`'s) -/
theorem mid_slot (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    {a : Nat} (v : Nat) (h1 : (s.regs 4).toNat - (232 + kc) ≤ a)
    (hm : a + 8 ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 96 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 8) :
    Mid R kc L s zp zc st xp xl xc n (M.writeLE a 8 v) L1 b1 p l c q ql qc ∧
      (∀ k, k ≤ c → (M.writeLE a 8 v).readLE p (8 * k) = M.readLE p (8 * k)) ∧
      (∀ k, k ≤ qc → (M.writeLE a 8 v).readLE q (8 * k) = M.readLE q (8 * k)) := by
  have hK := sp_K hpre
  have hstw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨hfw, hrt, hz, hzz, r⟩ := hmid
  have e0 : stW (M.writeLE a 8 v) st = stW M st := slot_other (by omega)
  have e1 : stLen (M.writeLE a 8 v) st = stLen M st := slot_other (by omega)
  have e2 : stCap (M.writeLE a 8 v) st = stCap M st := slot_other (by omega)
  have hacc : ∀ a' k w, (M.writeLE a 8 v).accessible a' k w = M.accessible a' k w :=
    fun a' k w => Arm64.Memory.accessible_writeLE _ _ _ _ _ _ _
  exact ⟨⟨fw2_slot hfw v hm (by omega), rtM_slot hpre hrt h1 (by omega),
    own_mono hz (LiveExt.refl R L1) hacc e0 e1 e2, own_mono hzz (LiveExt.refl R L1) hacc e0 e1 e2, r⟩,
    fun k hk => own_read1 hz h1 (by omega) hk, fun k hk => own_read1 hzz h1 (by omega) hk⟩

end

end FvModexp.Amd64.ModInv
