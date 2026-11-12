import FvModexp.Proofs.Arm64.Exp.P2PreSq
import FvModexp.Proofs.Common.RotA64

/-!
# `buildPrecomputationWindowModPower2` (arm64): loop head (`i < len`) → `nat.sqr` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

/-- the round locals stored at the loop body's start (`24 i` at `sp - 72`, `i` at `sp - 88`, `&powers[i]` at `sp - 16`,
`24 i + 24` at `sp - 80`), in the form the run produces -/
@[reducible] def memH (s : State) (M : Memory) (pw i : Nat) : Memory :=
  (((M.writeLE (s.sp.toNat - 208 + 136) 8 (8 * i + 2 * (8 * i))).writeLE (s.sp.toNat - 208 + 120) 8 i).writeLE
    (s.sp.toNat - 208 + 192) 8 (8 * i + 2 * (8 * i) + pw)).writeLE (s.sp.toNat - 208 + 128) 8 (8 * i + 2 * (8 * i) + 24)

set_option maxRecDepth 20000 in
theorem rs_head (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 i : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1)
    (hd : ∀ j, j < i → PwD M pw bp lm (natVal s.mem x xl) j) (ht : ∀ j, i ≤ j → j < pl → PwT M pw bp lm j)
    (hip : i + 2 ≤ pl) : RS R kc L st pw pl lm s (natVal s.mem x xl) bp (memH s M pw i) L1 b1 i i := by
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hK := hf.w.sp
  have hpww := hf.pww
  have hpw48 := hf.pw48
  have hs48 := hf.sp48
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hpww hs48
  have hnb : 0 < NB pl lm := Nat.mul_pos (by omega) (by omega)
  have hbw := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
    (by simp only; omega)
  simp only [K, A] at hbw
  have hrd : ∀ c n, ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
      (memH s M pw i).readLE c n = M.readLE c n := by
    intro c n h
    simp only [memH]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hpin : ∀ j, j < i → bp + 8 * (j * W lm) + 8 * (2 * W lm) ≤ bp + 8 * NB pl lm := fun j hj =>
    pw_in (by omega)
  have o : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat - 64 ∨ (s.sp.toNat - 40 ≤ a ∧ a + 8 ≤ s.sp.toNat - 8) →
      OwnW s pw pl a 8 := fun a h1 h2 => by
    simp only [OwnW]; omega
  refine ⟨ctx_own (ctx_own (ctx_own (ctx_own hc hf _ (o _ (by omega) (by omega))) hf _ (o _ (by omega) (by omega)))
      hf _ (o _ (by omega) (by omega))) hf _ (o _ (by omega) (by omega)),
    fun j hj => pwd_keep (hd j hj) (fun c n h1 h2 => hrd c n (Or.inl ⟨by omega, by omega⟩))
      (fun c n h1 h2 _ => hrd c n (Or.inr ⟨by omega, by have := hpin j hj; omega⟩)),
    fun j hj hjp => pwt_keep (ht j (by omega) hjp) (fun c n h1 h2 => hrd c n (Or.inl ⟨by omega, by omega⟩)), ?_⟩
  simp only [Lo, memH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 88 = s.sp.toNat - 208 + 120 by omega, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 72 = s.sp.toNat - 208 + 136 by omega, Memory.readLE_writeLE_self]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show s.sp.toNat - 80 = s.sp.toNat - 208 + 128 by omega, Memory.readLE_writeLE_self]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show s.sp.toNat - 16 = s.sp.toNat - 208 + 192 by omega, Memory.readLE_writeLE_self]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segH (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypR impl R ns stkS aboveS sqC) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (kA : JA impl R kc sqC mlC b L st pw pl lm x xl s i) (hip : i + 2 ≤ pl) :
    HeadJ impl R kc sqC mlC b L st pw pl lm x xl s i := by
  intro S bp L1 b1 hpc hsp h28 h29 h18 h0 h7 h9 hc hd ht he h2 hi hb
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; exact hw
  have hpw48 := hf.pw48
  have hpwa : S.mem.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, e2, -, e4, -, -, -, e8⟩ := hc.sl
  obtain ⟨t0, t1, t2⟩ := ht i (Nat.le_refl _) (by omega)
  obtain ⟨d0, d2, d1, -, -⟩ := hd (i / 2) (by omega)
  have f160 : S.mem.readLE (s.sp.toNat - 208 + 160) 8 = pl := by
    rw [show s.sp.toNat - 208 + 160 = s.sp.toNat - 48 by omega]; exact e8
  have f232 : S.mem.readLE (s.sp.toNat - 208 + 232) 8 = pl := by
    rw [show s.sp.toNat - 208 + 232 = s.sp.toNat + 24 by omega]; exact e4
  have f216 : S.mem.readLE (s.sp.toNat - 208 + 216) 8 = st := by
    rw [show s.sp.toNat - 208 + 216 = s.sp.toNat + 8 by omega]; exact e2
  have hi63 : i < 2 ^ 63 := by omega
  have hs63 : BitVec.ofNat 64 i >>> 63 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
  have hasr : (BitVec.ofNat 64 i).sshiftRight 1 = BitVec.ofNat 64 (i / 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.2 (by rw [BitVec.toNat_ofNat]; omega)),
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hg63 := RotA64.getLsbD63 hi63
  have hrot := RotA64.rot1_low hi63
  have hq1 : i / 2 < pl := by omega
  have hq2 : i < pl := by omega
  have hq3 : i + 1 < pl := by omega
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  have m0 : S.mem.readLE (pw + (8 * i + 2 * (8 * i))) 8 = bp + 8 * (i * W lm) := by
    rw [show pw + (8 * i + 2 * (8 * i)) = pw + 24 * i by omega]; exact t0
  have m1 : S.mem.readLE (8 * i + 2 * (8 * i) + (pw + 8)) 8 = W lm := by
    rw [show 8 * i + 2 * (8 * i) + (pw + 8) = pw + 24 * i + 8 by omega]; exact t1
  have m2 : S.mem.readLE (8 * i + 2 * (8 * i) + (pw + 8 + 8)) 8 = 2 * W lm := by
    rw [show 8 * i + 2 * (8 * i) + (pw + 8 + 8) = pw + 24 * i + 16 by omega]; exact t2
  have m4 : S.mem.readLE (pw + (8 * (i / 2) + 2 * (8 * (i / 2)))) 8 = bp + 8 * (i / 2 * W lm) := by
    rw [show pw + (8 * (i / 2) + 2 * (8 * (i / 2))) = pw + 24 * (i / 2) by omega]; exact d0
  have m5 : S.mem.readLE (8 * (i / 2) + 2 * (8 * (i / 2)) + (pw + 8)) 8 = S.mem.readLE (pw + 24 * (i / 2) + 8) 8 := by
    rw [show 8 * (i / 2) + 2 * (8 * (i / 2)) + (pw + 8) = pw + 24 * (i / 2) + 8 by omega]
  have m6 : S.mem.readLE (8 * (i / 2) + 2 * (8 * (i / 2)) + (pw + 8 + 8)) 8 = W lm := by
    rw [show 8 * (i / 2) + 2 * (8 * (i / 2)) + (pw + 8 + 8) = pw + 24 * (i / 2) + 16 by omega]; exact d2
  have hxl : (memH s S.mem pw i).readLE (pw + 24 * (i / 2) + 8) 8 = S.mem.readLE (pw + 24 * (i / 2) + 8) 8 := by
    simp only [memH]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  unfold Goal
  janus_run [f160, f232, f216, hi63, hs63, hasr, hg63, hrot, m0, m1, m2, m4, m5, m6] until [1815584]
  refine callSqrH hap hns hnf hsq hkS haS hsm hkc hpre kA (rs_head hpre hkc hc hd ht hip) he h2 hip hb _
    ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hxl ?_ ?_
  all_goals janus_simp

end

end FvModexp.Arm64.P2Pre
