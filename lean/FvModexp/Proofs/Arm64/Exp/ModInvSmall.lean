import FvModexp.Proofs.Arm64.Exp.ModInvSeg
import FvModexp.Proofs.Common.GenReg
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): `n ≤ 64` (nat.go:1301-1304) (agent infra)

`k0 &= (1 << n) - 1; return z.setWord(k0)`: `z[:0]` when the masked `k0` is zero, else `z.make(1)` (`z[:1]`, or
`makeslice(Word, 1, 1)` when `cap z = 0`) with `z[0] = k0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

/-- the mask `k0 & ((1 << n) - 1)` for `1 ≤ n ≤ 64` (`CSEL LO` picks `0` for `n = 64`) -/
theorem mask_eq (k n : Nat) (hk : k < 2 ^ 64) (hn1 : 1 ≤ n) (hn : n ≤ 64) :
    (BitVec.ofNat 64 k &&& (if n < 64 then BitVec.ofNat 64 (2 ^ (n % 64)) else 0#64) - 1#64).toNat = k % 2 ^ n := by
  rw [BitVec.toNat_and]
  have hm : ((if n < 64 then BitVec.ofNat 64 (2 ^ (n % 64)) else 0#64) - 1#64).toNat = 2 ^ n - 1 := by
    split
    · rename_i h
      have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) h
      have h2 := Nat.one_le_two_pow (n := n)
      rw [Nat.mod_eq_of_lt h, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · rename_i h
      rw [show n = 64 by omega]; rfl
  rw [hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.and_two_pow_sub_one_eq_mod]

theorem val_small (X n : Nat) (hn : n ≤ 64) : val X n = Exp.newton (min 64 n) (X % Exp.B) % 2 ^ n := by
  unfold val Exp.modularInverseModPowerOfTwo; rw [if_pos hn]

/-- the window parts `winA` lie inside the window `win` -/
theorem outside_winA {s : State} {stk above a n : Nat} (h8 : 8 ≤ stk) (h : Outside a n (win s stk above)) :
    Outside a n (winA s stk above) := by
  simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxRecDepth 20000 in
/-- the post when only the stack (`winA`) and possibly `z`'s array were written, `z` kept (`L' = L`,
`b' = b + stkR H s.mem st`: the reserve is refunded, the capacity unchanged) -/
theorem post_keep {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} (hkc : 4608 ≤ kc)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (zr : List (Nat × Nat))
    (hzr : zr = [] ∨ (0 < zc ∧ zr = [(zp, zp + 8 * zc)])) (s' : State)
    (hF : MemFrame s.mem s'.mem (winA s (K kc) A ++ zr)) (hinv : R.inv (b + stkR H s.mem st) L (s.regs 28).toNat (view R.rt L s'.mem))
    {l' : Nat} (e0 : (s'.regs 0).toNat = zp) (e1 : (s'.regs 1).toNat = l') (e2 : (s'.regs 2).toNat = zc)
    (hv : natVal s'.mem zp l' = val (natVal s.mem xp xl) n) (hn : NatNorm s'.mem zp l') (hlc : l' ≤ zc) :
    Post R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, ⟨hzc40, hzlive, -⟩, -, -, -, -, -, -, -, -,
    ⟨hst, hstw, -⟩, -, hsz, -, -, -, -, -, -⟩ := hpre'
  have hFb : MemFrame s.mem s'.mem (R.rt ++ winA s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) := by
    refine hF.mono fun a k h => ?_
    simp only [outside_append] at h ⊢
    refine ⟨h.1.1.2, ?_⟩
    rcases hzr with rfl | ⟨-, rfl⟩
    · simp
    · exact h.1.2
  have hst' : Outside st 24 (winA s (K kc) A ++ zr) := by
    simp only [outside_append]
    refine ⟨outside_winA (by simp only [K]; omega) hstw, ?_⟩
    rcases hzr with rfl | ⟨hc, rfl⟩
    · simp
    · have := (hsz (by omega)).1; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  obtain ⟨-, k0, -, k2⟩ := stkOK_frame hst hF hst' (LiveExt.refl R L)
  refine ⟨zp, l', zc, e0, e1, e2, hv, hn, hlc, hzc40, L, b + stkR H s.mem st, LiveExt.refl R L,
    by rw [stkR_congr k2]; omega, hinv, ?_,
    Or.inl ⟨rfl, rfl⟩, ⟨stackBack_frame hst hF hst' (LiveExt.refl R L), fun hn => absurd ⟨k0, k2⟩ hn⟩, hFb, ?_,
    fun _ hn => absurd ⟨k0, k2⟩ hn⟩
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hzlive hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · refine Expmc.liveFrame_of_frame hF fun a k hin hws => ?_
    simp only [outside_append] at hws ⊢
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr, h1, h2⟩ := hin
      have := hLs r hr
      simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega
    · rcases hzr with rfl | ⟨-, rfl⟩
      · simp
      · exact hws.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem small (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (s : State) (hkc : 4608 ≤ kc) :
    JS impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S hpre hs hpc hsp h28 h18 h0 h2 h7 h10 hF hrg hfw
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgrt, hLs, hro⟩, hsv, -, hn1, hn2, hzl, hzp, hzc0, ⟨hzc40, hzlive, hzw⟩,
    -⟩ := hpre'
  simp only [K, A] at hw hout hb' ha hga
  rw [show (1797104 + 0x64 : Nat) = 1797204 from rfl] at hpc
  obtain ⟨f1, f2⟩ := hfw
  unfold Goal
  janus_run [hs] until [1797736]
  gen_reg 3 as m with hm
  have hk0 : k0 s xp xl n < 2 ^ 64 := by
    unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
  have hmv : m.toNat = k0 s xp xl n % 2 ^ n := by rw [← hm]; exact mask_eq _ n hk0 hn1 hs
  clear hm
  by_cases hv : k0 s xp xl n % 2 ^ n = 0
  · have hm0 : m = 0#64 := by apply BitVec.eq_of_toNat_eq; rw [hmv, hv]; rfl
    have f2' : S.mem.readLE (s.sp.toNat - 240 - 8) 8 = (s.regs 29).toNat := by
      rw [show s.sp.toNat - 240 - 8 = s.sp.toNat - 248 by omega]; exact f2
    have hinv0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    janus_run [hm0, f1, f2']
    refine ⟨?_, post_keep (l' := 0) hkc hpre [] (Or.inl rfl) _ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inl rfl) (Nat.zero_le _)⟩
    · have hsl := s.sp.isLt
      have hal' : 240 ≤ s.sp.toNat := by omega
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simpa using hF
    · exact inv_win (by simp only [K]; omega) hout hF hinv0
    · janus_simp
    · janus_simp
    · janus_simp
    · rw [val_small _ _ hs]; simp only [k0] at hv; rw [hv]; rfl
  · have hmz : ¬ m = 0#64 := fun h => hv (by rw [← hmv, h]; rfl)
    have f2' : S.mem.readLE (s.sp.toNat - 240 - 8) 8 = (s.regs 29).toNat := by
      rw [show s.sp.toNat - 240 - 8 = s.sp.toNat - 248 by omega]; exact f2
    have hinv0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    by_cases hz : zc = 0
    · omega
    · have hz' : ¬ BitVec.ofNat 64 zc = 0#64 := by
        intro h; apply hz; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
      obtain ⟨z8, zh, zacc, z48⟩ := hzlive (by omega)
      have hza : S.mem.accessible zp 8 true = true := by
        rw [hF.accessible]; exact Memory.accessible_sub _ zacc (Or.inr rfl) (Nat.le_refl _) (by omega)
      obtain ⟨hzo, -⟩ := hzw (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at hzo
      have g1 : (S.mem.writeLE zp 8 m.toNat).readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat := by
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [K, A] at hzo; omega)]; exact f1
      have g2 : (S.mem.writeLE zp 8 m.toNat).readLE (s.sp.toNat - 240 - 8) 8 = (s.regs 29).toNat := by
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [K, A] at hzo; omega)]; exact f2'
      have hl48 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      janus_run [hmz, hz', g1, g2, hl48]
      have hzh : Held R L zp 8 := zh.sub (Nat.le_refl _) (by omega)
      refine ⟨?_, post_keep (l' := 1) hkc hpre [(zp, zp + 8 * zc)] (Or.inr ⟨by omega, rfl⟩) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (by omega)⟩
      · have hsl := s.sp.isLt
        have hal' : 240 ≤ s.sp.toNat := by omega
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · refine MemFrame.writeLE_inRanges (hF.mono fun a k h => ?_) _ ⟨(zp, zp + 8 * zc), by simp, by omega, by omega⟩
        simp only [outside_append] at h; exact h.1
      · exact inv_store_held (inv_win (by simp only [K]; omega) hout hF hinv0) hzh
      · janus_simp
      · janus_simp
      · janus_simp
      · show Memory.readLE _ zp (8 * 1) = _
        rw [Nat.mul_one, Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := m.isLt; simpa using this), hmv,
          val_small _ _ hs]
      · refine Or.inr ?_
        show Memory.readLE _ (zp + 8 * (1 - 1)) 8 ≠ 0
        rw [show zp + 8 * (1 - 1) = zp by omega, Memory.readLE_writeLE_self,
          Nat.mod_eq_of_lt (by have := m.isLt; simpa using this), hmv]
        exact hv

end FvModexp.Arm64.ModInv
