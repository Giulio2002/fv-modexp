import FvModexp.Proofs.Arm64.Exp.ModInvSeg3
import FvModexp.Proofs.Arm64.Exp.ModInvZZ

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): facts at the loop head after `zz.make` + `setWord` (agent infra)

Pure lemmas for `JM → J2` (nat.go:1322-1325): `dl_rt` (the read-only data is still loaded at any memory the runtime
facts describe), `newton64_pos` (`k0 ≠ 0` for odd `x`), `zz_j2` (from the facts after the `zz` allocation and the
store `z[0] = k0` to `J2`'s hypotheses).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp

/-- the Newton start value `newton 64 (x mod 2^64)` of an odd `x` is non-zero (it inverts `x` mod `2^64`) -/
theorem newton64_pos (x : Nat) (hx : x % 2 = 1) : 0 < Exp.newton 64 (x % Exp.B) := by
  have hx0 : x % Exp.B % 2 = 1 := by
    rw [Exp.B_def, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 64))]; exact hx
  have hxB : x % Exp.B < Exp.B := Nat.mod_lt _ Exp.B_pos
  have hN := Exp.newtonLoop_spec 64 (x % Exp.B) hxB (by omega) 64 0
    ((x % Exp.B + Exp.B - 1) % Exp.B) ((2 + Exp.B - x % Exp.B % Exp.B) % Exp.B) (by simp)
    (Exp.newton_init (x % Exp.B) hx0 hxB) (by
      have hB : Exp.B = 18446744073709551616 := Exp.B_eq
      have : (x % Exp.B + Exp.B - 1) % Exp.B = x % Exp.B - 1 := by rw [hB] at hxB ⊢; omega
      rw [this]; simp; omega)
  unfold Exp.newton
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0, Nat.mul_zero, Nat.zero_mod] at hN
  simp at hN

set_option maxRecDepth 20000 in
/-- the read-only data is still loaded at a memory the runtime facts describe -/
theorem dl_rt {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) : Extracted.program.DataLoaded M := by
  obtain ⟨⟨-, ⟨-, hb', -, hw⟩, hd, -, -, -, -, hro⟩, -, -, -, -, -, -, hzc0, ⟨-, hzlive, -⟩, -, -, -, -, -, -, -, -,
    ⟨⟨-, -, hsta, -, hstl, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨r0, F0, -⟩ := hrt
  refine dataLoaded_frame hd r0 hro (by simpa only [List.append_assoc] using F0) ?_
  intro r hr hlt
  simp only [List.mem_append, winA, ExpHyp.stWs, stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [K, A] at hw hb'
  rcases hr with (rfl | rfl) | rfl | rfl | rfl
  · dsimp only [K, A] at hlt ⊢
    exact Memory.accessible_mono _ hw (by omega) (by omega)
  · dsimp only [K, A] at hlt ⊢
    exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact Memory.accessible_mono _ (hzlive hzc0).2.2.1 (by dsimp only; omega) (by dsimp only; omega)
  · exact Memory.accessible_mono _ hsta (by dsimp only; omega) (by dsimp only; omega)
  · dsimp only at hlt ⊢
    exact Memory.accessible_mono _ (hstl (by omega)).2.2.1 (by omega) (by omega)

theorem budget_aux {b b1 x y z r a R : Nat} (h1 : b - x + R ≤ b1) (h2 : b1 - y ≤ b1 - r) (h3 : y ≤ a) (h4 : z = a)
    (h5 : x + z ≤ b) : b - (x + z) + R ≤ b1 - r := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the facts at `J2` after `zz := nat(nil).make(2·numWords)` and the store `z[0] = k0` (pure) -/
theorem zz_j2 {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hkc : 4608 ≤ kc) (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {M m : Memory}
    {L1 : List (Nat × Nat)} {b1 zp' zc' q r k : Nat}
    (hfw : Fw1 s M st xp xl xc n k) (hrt : RtM R kc L s zp zc st M L1 b1) (hb : b - makeCost (NW n + 1) + stkR H M st ≤ b1)
    (hown : Own R kc L L1 s zp zc st xp xl M zp' zc') (hcap : NW n + 1 ≤ zc') (hk : k < 2 ^ 64)
    (hap : AllocPostZ R L1 b1 (s.regs 28).toNat (s.sp.toNat - 240) (NW n) M m q r) :
    Fw2 s (m.writeLE zp' 8 k) st xp xl xc n ∧
      RtM R kc L s zp zc st (m.writeLE zp' 8 k) (L1 ++ [(q, q + r)]) (b1 - r) ∧
      b - spent sqrC mulC xl n 1 + stkR H (m.writeLE zp' 8 k) st ≤ b1 - r ∧
      Own R kc L (L1 ++ [(q, q + r)]) s zp zc st xp xl (m.writeLE zp' 8 k) zp' zc' ∧
      Own R kc L (L1 ++ [(q, q + r)]) s zp zc st xp xl (m.writeLE zp' 8 k) q (2 * NW n + 4) ∧
      Apart zp' (8 * zc') q (8 * (2 * NW n + 4)) ∧ natVal (m.writeLE zp' 8 k) zp' (NW n + 1) % Exp.B = k := by
  have hcostQ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  have hrt' := hrt
  obtain ⟨⟨-, ⟨-, hal, -, -⟩, -, hout, -, hgrt, hLs, -⟩, -, -, hn1, hn2, -, -, -, -, -, -, -, -,
    ⟨-, -, -, hxh, -⟩, -, -, -, ⟨-, hstw, -, -⟩, -, -, hcost, -, -, -, -⟩ := hpre
  obtain ⟨hMF, hLF, hrg, hIn, hAp, hle, hacc, h8, hsz, hbr, hinv⟩ := hap
  obtain ⟨-, -, -, LE0, -, hstk, -, -⟩ := hrt'
  have hmc : makeCost (2 * NW n) = allocCost (8 * (2 * NW n + 4)) := by
    unfold makeCost makeCap; rw [if_neg (show ¬ (2 * NW n = 1) by simp only [NW]; omega)]
  have hbl := blockSize_le_allocCost (8 * (2 * NW n + 4)) true
  simp only [K, A] at hal hout hstw
  have hws : ∀ a k, Outside a k (winA s (240 + kc) 72) →
      Outside a k [(s.sp.toNat - 240 - 4096, s.sp.toNat - 240 - 8), (s.sp.toNat - 240 + 8, s.sp.toNat - 240 + 32),
        (s.sp.toNat - 240 + 96, s.sp.toNat - 240 + 104), (s.sp.toNat - 240 + 136, s.sp.toNat - 240 + 144)] := by
    intro a k h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hwo : Outside (s.sp.toNat - (240 + kc)) (240 + kc + 72) R.rt := hout
  have hLF' : LiveFrame M m L1 [(s.sp.toNat - 240 - 4096, s.sp.toNat - 240 - 8),
      (s.sp.toNat - 240 + 8, s.sp.toNat - 240 + 32), (s.sp.toNat - 240 + 96, s.sp.toNat - 240 + 104),
      (s.sp.toNat - 240 + 136, s.sp.toNat - 240 + 144)] :=
    ⟨fun a k h _ => hLF.readLE a k h (by simp only [outside_nil])⟩
  have hLE : LiveExt R L1 (L1 ++ [(q, q + r)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hhdr : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = M.readLE (st + j) 8 := by
    intro j hj
    refine Held.readLE ((hstk.2.1).sub (by omega) (by omega)) hMF hLF' ?_
    have h := hstw.of_sub (a := st + j) (n := 8) (by omega) (by omega)
    exact hws _ _ (by simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega)
  have e0 : stW m st = stW M st := by have := hhdr 0 (by omega); simpa using this
  have e1 : stLen m st = stLen M st := hhdr 8 (by omega)
  have e2 : stCap m st = stCap M st := hhdr 16 (by omega)
  have hsb : StackBack R L1 (L1 ++ [(q, q + r)]) st M m := stackBack_hdr hstk hMF e0 e1 e2 hLE
  have hrt1 : RtM R kc L s zp zc st m (L1 ++ [(q, q + r)]) (b1 - r) := by
    refine rtM_call hrt hrg hMF ?_ hLF' ?_ hLE hinv hsb (ain_keep e0 e2)
    · intro a k h; simp only [outside_append] at h ⊢; exact ⟨h.1.1.1, hws a k h.1.1.2⟩
    · intro a k hin _
      obtain ⟨q', hq, h1, h2⟩ := hin
      have := hLs q' hq
      simp only [win, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hown1 : Own R kc L (L1 ++ [(q, q + r)]) s zp zc st xp xl m zp' zc' :=
    own_mono hown hLE (fun a k w => by rw [hMF.accessible]) e0 e1 e2
  -- the fresh `zz`
  have hc : 8 * (2 * NW n + 4) ≤ r := hsz
  have hIn' : InRanges q (8 * (2 * NW n + 4)) R.rt := hIn.sub (Nat.le_refl _) (by omega)
  have hAp1 : ApartAll q (8 * (2 * NW n + 4)) L1 := fun q' hq => by
    have := hAp q' hq; unfold Apart at this ⊢; omega
  have hAp' : ApartAll q (8 * (2 * NW n + 4)) L := apartAll_old LE0 hAp1
  have hw1 := fresh_out hIn' hwo
  unfold Apart at hw1
  have hown2 : Own R kc L (L1 ++ [(q, q + r)]) s zp zc st xp xl m q (2 * NW n + 4) := by
    refine ⟨by simp only [NW]; omega, by omega, fun _ => ⟨h8, Or.inl ⟨(q, q + r), by simp, by omega, by simp only; omega⟩,
      hacc, by omega⟩, Or.inr ⟨hIn', hAp'⟩, by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega,
      fresh_out hIn' hgrt, fresh_apart hIn' hAp1 (LE0.held hxh), fun _ => ⟨fresh_apart hIn' hAp1 hstk.2.1, ?_⟩, ?_⟩
    · rw [e0, e1, e2]
      intro hlt
      obtain ⟨-, hh, -, -⟩ := hstk.2.2.2.2.1 (by omega)
      exact fresh_apart hIn' hAp1 (hh.sub (by omega) (by rw [Nat.mul_sub]; omega))
    · intro _ _ hcap
      rw [e2] at hcap; rw [e0, e2]
      exact fresh_apart hIn' hAp1 (hstk.2.2.2.2.1 hcap).2.1
  -- `z[0] = k0`
  have hzc0 : 0 < zc' := by omega
  obtain ⟨-, hzh, -, -⟩ := hown.2.2.1 hzc0
  have hzq : Apart zp' (8 * zc') q (8 * (2 * NW n + 4)) := (fresh_apart hIn' hAp1 hzh).symm
  obtain ⟨hzs, -⟩ := hown1.2.2.2.2.2.2.2.1 (by omega)
  have hzo := hown1.2.2.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzo
  unfold Apart at hzs
  have f0 : stW (m.writeLE zp' 8 k) st = stW m st := Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have f1 : stLen (m.writeLE zp' 8 k) st = stLen m st := Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have f2 : stCap (m.writeLE zp' 8 k) st = stCap m st := Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hacw : ∀ a k' w, (m.writeLE zp' 8 k).accessible a k' w = m.accessible a k' w :=
    fun a k' w => Memory.accessible_writeLE _ _ _ _ _ _ _
  have hrd : ∀ a, s.sp.toNat - (240 + kc) ≤ a → a + 8 ≤ s.sp.toNat - 240 - 4096 ∨
      (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232) ∨
      (s.sp.toNat - 240 + 32 ≤ a ∧ a + 8 ≤ s.sp.toNat - 240 + 96) ∨
      (s.sp.toNat - 240 + 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 240 + 136) ∨
      (s.sp.toNat - 240 + 144 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72) →
      (m.writeLE zp' 8 k).readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    refine hMF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwo.of_sub h1 (by omega), by omega, by omega, by omega, by omega⟩
  obtain ⟨⟨g1, g2⟩, g3, g4, g5, g6, g7, g8, g9, -⟩ := hfw
  have hv : natVal (m.writeLE zp' 8 k) zp' 1 = k := by
    rw [show (1 : Nat) = 0 + 1 from rfl, natVal_succ, natVal_zero, Nat.mul_zero, Nat.add_zero, Nat.pow_zero,
      Nat.one_mul, Memory.readLE_writeLE_self, Nat.zero_add, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]
    exact Nat.mod_eq_of_lt hk
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rtM_store hrt1 hown1 (Nat.le_refl _) (by omega), ?_,
    own_mono hown1 (LiveExt.refl _ _) hacw f0 f1 f2, own_mono hown2 (LiveExt.refl _ _) hacw f0 f1 f2, hzq, ?_⟩
  · rw [hrd _ (by omega) (by omega)]; exact g1
  · rw [hrd _ (by omega) (by omega)]; exact g2
  · rw [hrd _ (by omega) (by omega)]; exact g3
  · rw [hrd _ (by omega) (by omega)]; exact g4
  · rw [hrd _ (by omega) (by omega)]; exact g5
  · rw [hrd _ (by omega) (by omega)]; exact g6
  · rw [hrd _ (by omega) (by omega)]; exact g7
  · rw [hrd _ (by omega) (by omega)]; exact g8
  · rw [hrd _ (by omega) (by omega)]; exact g9
  · have e : spent sqrC mulC xl n 1 = makeCost (NW n + 1) + makeCost (2 * NW n) := by
      simp only [spent]; rfl
    rw [e, stkR_congr (f2.trans e2)]
    exact budget_aux hb hbr hbl hmc (by simp only [cost] at hcostQ; omega)
  · rw [Exp.natVal_prefix _ _ 1 (NW n + 1) (by omega), Nat.pow_one] at hv; exact hv

end FvModexp.Arm64.ModInv
