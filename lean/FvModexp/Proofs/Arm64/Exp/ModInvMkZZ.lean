import FvModexp.Proofs.Arm64.Exp.ModInvJ2

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `JM` → `J2` (nat.go:1322-1325) (agent infra)

From `JM` (`+0x15c`): `zz := nat(nil).make(2·numWords)` (`2·numWords ≥ 4`: the `makeslice` path at `+0x1e0`, the small
lemma `zzalloc`), `z.setWord(k0)` (`k0 ≠ 0`, `cap z ≥ numWords + 1`: the store `z[0] = k0`, `setw`), `i = 2`, the jump
to the loop head `J2` with `j = 1` and `Z0 = natVal z (numWords + 1)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- stack-slot stores keep an owned array owned -/
theorem own_stk {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 : List (Nat × Nat)} {p c : Nat}
    (h : Own R kc L L1 s zp zc st xp xl M p c) (hF : MemFrame M M' (winA s (K kc) A)) :
    Own R kc L L1 s zp zc st xp xl M' p c := by
  obtain ⟨⟨-, ⟨-, hal, -, -⟩, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hstw, -, -⟩, -⟩ := hpre
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hal hstw
  have hr : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    hF.readLE _ _ (by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega)
  have e0 : stW M' st = stW M st := by have := hr 0 (by omega); simpa using this
  exact own_mono h (LiveExt.refl _ _) (fun a k w => by rw [hF.accessible]) e0 (hr 8 (by omega)) (hr 16 (by omega))

/-- the memory after the three spills at `+0x17c` (`cap z` to `SP + 192`, `numWords + 1` to `SP + 88`, `z.ptr` to
`SP + 208`, in-frame `SP = sp`) -/
@[reducible] def mem3 (M : Memory) (sp v1 v2 v3 : Nat) : Memory :=
  ((M.writeLE (sp + 192) 8 v1).writeLE (sp + 88) 8 v2).writeLE (sp + 208) 8 v3

set_option maxRecDepth 20000 in
theorem stk3 {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 p c k : Nat}
    (hfw : Fw1 s M st xp xl xc n k) (hrt : RtM R kc L s zp zc st M L1 b1) (hown : Own R kc L L1 s zp zc st xp xl M p c)
    (v1 v2 v3 : Nat) :
    Fw1 s (mem3 M (s.sp.toNat - 240) v1 v2 v3) st xp xl xc n k ∧
      RtM R kc L s zp zc st (mem3 M (s.sp.toNat - 240) v1 v2 v3) L1 b1 ∧
      Own R kc L L1 s zp zc st xp xl (mem3 M (s.sp.toNat - 240) v1 v2 v3) p c := by
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hpre.1
  have hb2 : 240 + kc ≤ s.sp.toNat := hb'
  clear hb'
  have hF : MemFrame M (mem3 M (s.sp.toNat - 240) v1 v2 v3) (winA s (K kc) A) := by
    refine (((MemFrame.refl M _).writeLE_inRanges _ ?_).writeLE_inRanges _ ?_).writeLE_inRanges _ ?_ <;>
      exact ⟨_, List.mem_cons_self .., by dsimp only [K]; omega, by dsimp only; omega⟩
  have hreg : (mem3 M (s.sp.toNat - 240) v1 v2 v3).regions = M.regions := by
    simp only [mem3, Memory.regions_writeLE]
  obtain ⟨⟨f1, f2⟩, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hfw
  have hr : ∀ a, (a + 8 ≤ s.sp.toNat - 240 + 88 ∨ s.sp.toNat - 240 + 96 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 240 + 192 ∨ s.sp.toNat - 240 + 200 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 240 + 208 ∨ s.sp.toNat - 240 + 216 ≤ a) →
      (mem3 M (s.sp.toNat - 240) v1 v2 v3).readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    simp only [mem3]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rtM_stk hpre hrt hF hreg, own_stk hpre hown hF⟩
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f1
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f2
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f3
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f4
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f5
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f6
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f7
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f8
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f9
  · rw [hr _ (by omega) (by omega) (by omega)]; exact f10

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
theorem mkzz (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4608 ≤ kc)
    (kJ : J2 impl R kc sqrC mulC b L zp zl zc st xp xl xc n s) :
    JM impl R kc sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S zp' zc' L1 b1 hpre hn hpc hsp h28 h18 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hfw hrt hb hown hcap
  unfold Goal
  have hn2 := hpre.2.2.2.2.1
  have hsv := hpre.2.1
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (240 + kc)) (240 + kc + 72) true = true := by
    rw [hrt.2.1.accessible]; exact hw
  have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hty : Outside wT 16 R.rt := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx1 : natVal s.mem xp xl % 2 = 1 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hnw1 : 2 ≤ NW n := by simp only [NW]; omega
  have hnw2 : NW n ≤ 2 ^ 12 := by simp only [NW]; omega
  have hk0 : k0 s xp xl n < 2 ^ 64 := by
    unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
  have hk0p : 0 < k0 s xp xl n := by
    unfold k0; rw [show min 64 n = 64 by omega]; exact newton64_pos _ hx1
  have hok : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * NW n, 2 * NW n + 4] :=
    hsv.1 _ _ _ (by omega)
  have hmc : makeCost (2 * NW n) = allocCost (8 * (2 * NW n + 4)) := by
    unfold makeCost makeCap; rw [if_neg (show ¬ (2 * NW n = 1) by omega)]
  have hbl := blockSize_le_allocCost (8 * (2 * NW n + 4)) true
  have hbs : blockSize (8 * (2 * NW n + 4)) true ≤ b1 := by simp only [cost] at hcost; omega
  have hzc0 : 0 < zc' := by omega
  have hzlt := hown.1
  have hzp' := hown.2.1
  have hadd : BitVec.ofNat 64 (NW n) + BitVec.ofNat 64 (NW n) = BitVec.ofNat 64 (2 * NW n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [show (1797104 + 0x15c : Nat) = 1797452 from rfl] at hpc
  janus_run [hadd] until [1797584]
  obtain ⟨hfw3, hrt3, hown3⟩ := stk3 hkc hpre hfw hrt hown zc' (NW n + 1) zp'
  have hd3 := dl_rt hpre hrt3
  have he3 := env_rt hpre hrt3
  obtain ⟨ht8, ht0, hta⟩ := wT_facts hd3
  have hwt : Apart wT 16 (s.sp.toNat - 240 - kc) (kc + 312) := apart_of_data hd3 1 (by decide) (by decide) he3.2.2.2.1
  have hsp' : s.sp.toNat - 240 + 272 = s.sp.toNat + 32 := by omega
  refine zzalloc impl R hmk _ _ b1 L1 (s.regs 28).toNat (s.sp.toNat - 240) kc (NW n)
    (mem3 S.mem (s.sp.toNat - 240) zc' (NW n + 1) zp') (S.regs 18) (S.regs 29) he3 hkc (by omega) hnw2 ht8 ht0 hta hwt
    hty hok hbs hrt3.2.2.2.2.1 zp' (NW n + 1) zc' st xp xl xc n (n + 63) (NW n) (k0 s xp xl n)
    ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 _ rfl rfl ?h11 ?h18 ?h28 ?h29 rfl ?KZ
  case r0 =>
    simp only [mem3]; rw [Memory.readLE_writeLE_self, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt hzp'
  case r1 =>
    simp only [mem3]; rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  case r2 =>
    simp only [mem3]; rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  case r3 => rw [show s.sp.toNat - 240 + 272 = s.sp.toNat + 32 by omega]; exact hfw3.2.1
  case r4 => rw [show s.sp.toNat - 240 + 280 = s.sp.toNat + 40 by omega]; exact hfw3.2.2.1
  case r5 => rw [show s.sp.toNat - 240 + 288 = s.sp.toNat + 48 by omega]; exact hfw3.2.2.2.1
  case r6 => rw [show s.sp.toNat - 240 + 296 = s.sp.toNat + 56 by omega]; exact hfw3.2.2.2.2.1
  case r7 => rw [show s.sp.toNat - 240 + 304 = s.sp.toNat + 64 by omega]; exact hfw3.2.2.2.2.2.1
  case r8 => rw [show s.sp.toNat - 240 + 200 = s.sp.toNat - 40 by omega]; exact hfw3.2.2.2.2.2.2.1
  case r9 => rw [show s.sp.toNat - 240 + 128 = s.sp.toNat - 112 by omega]; exact hfw3.2.2.2.2.2.2.2.1
  case r10 => rw [show s.sp.toNat - 240 + 152 = s.sp.toNat - 88 by omega]; exact hfw3.2.2.2.2.2.2.2.2
  case h11 => simp [setReg]
  case h18 => simp [setReg]
  case h28 => simp [setReg, h28]
  case h29 => simp [setReg]
  case KZ =>
    intro S' m q r k1 k2 k13 k12 k11 k0' k1' k2' k3 k4 k5 k6 k7 k8 k9 k10 k18 k28 k29 kmem hap
    have hacc : m.accessible zp' 8 true = true := by
      rw [hap.1.accessible]
      exact Memory.accessible_mono _ (hown3.2.2.1 hzc0).2.2.1 (Nat.le_refl _) (by omega)
    refine setw impl _ _ zp' zc' (k0 s xp xl n) (s.sp.toNat - 240) m hk0p hk0 hzc0 (by omega) hzp' hacc S' k1 k2 k0'
      k2' k10 kmem ?KS
    intro S'' f1 f2 f3 f4 fr fm
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := zz_j2 hkc hpre hn hfw3 hrt3 hb hown3 hcap hk0 hap
    have fr' : ∀ i, i ≠ 0 → i ≠ 14 → i < 31 → S''.regs i = S'.regs i := fr
    have hz0i := Exp.z0_inv _ _ hx1 (show natVal (m.writeLE zp' 8 (k0 s xp xl n)) zp' (NW n + 1) % Exp.B = _ by
      rw [g7, k0, Nat.min_eq_left (by omega)])
    refine kJ 1 S'' zp' (NW n + 1) zc' q (2 * NW n) (2 * NW n + 4) _ _ hpre hn f1 f2 ?q28 ?q18 (by rw [f3])
      (by rw [fr' 1 (by decide) (by decide) (by decide), k1']) (by rw [fr' 2 (by decide) (by decide) (by decide), k2'])
      f4 (by rw [fr' 11 (by decide) (by decide) (by decide), k11])
      (by rw [fr' 12 (by decide) (by decide) (by decide), k12])
      (by rw [fr' 13 (by decide) (by decide) (by decide), k13])
      (by rw [fr' 3 (by decide) (by decide) (by decide), k3]) (by rw [fr' 4 (by decide) (by decide) (by decide), k4])
      (by rw [fr' 5 (by decide) (by decide) (by decide), k5]) (by rw [fr' 6 (by decide) (by decide) (by decide), k6])
      (by rw [fr' 7 (by decide) (by decide) (by decide), k7]) (by rw [fr' 8 (by decide) (by decide) (by decide), k8])
      (by rw [fr' 9 (by decide) (by decide) (by decide), k9])
      (by rw [fm]; exact g1) (by rw [fm]; exact g2) g3 (by rw [fm]; exact g4) (by rw [fm]; exact g5) hcap
      (Nat.le_refl _) hcap (by omega) (by omega) (Nat.le_refl _) (by rw [Nat.sub_self, Nat.pow_zero]; omega) g6 (by rw [fm]; exact hz0i)
    case q28 =>
      rw [fr' 28 (by decide) (by decide) (by decide), k28, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    case q18 => rw [fr' 18 (by decide) (by decide) (by decide), k18, h18]

end FvModexp.Arm64.ModInv
