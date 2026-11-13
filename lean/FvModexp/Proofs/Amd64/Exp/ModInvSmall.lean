import FvModexp.Proofs.Amd64.Exp.ModInvSeg
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `n ≤ 64` (nat.go:1301-1304) (agent infra s53; twin of
`Arm64/Exp/ModInvSmall`)

`k0 &= (1 << n) - 1; return z.setWord(k0)`:
```
+0x71    CMPQ R10, $0x40 ; JLS +0x316
+0x316   SBBQ DX, DX; MOVQ CX, BX; MOVQ R10, CX; MOVL $1, SI; SHLQ CL, SI   // (n < 64 ? 1 << n : 0) − 1
         ANDQ SI, DX; DECQ DX; ANDQ DX, R12; TESTQ R12, R12; JNE +0x339
+0x335   XORL CX, CX; JMP +0x370                                          // z[:0]
+0x339   TESTQ BX, BX; JNE +0x368 (cap z > 0: the pre excludes the `makeslice` path)
+0x368   MOVQ R12, (AX); MOVL $1, CX                                      // z[:1], z[0] = k0
+0x370   (AX, BX, CX) = (z.ptr, len, cap z); ADDQ $0xd8, SP; POPQ BP; RET
```
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

theorem mask64 (k : Nat) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k &&& 18446744073709551615#64 = BitVec.ofNat 64 (k % 2 ^ 64) := by
  rw [Nat.mod_eq_of_lt hk]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) hk

theorem maskLt (k n : Nat) (hk : k < 2 ^ 64) (hn : n < 64) :
    BitVec.ofNat 64 k &&& (18446744073709551615#64 &&& 1#64 <<< n) - 1#64 = BitVec.ofNat 64 (k % 2 ^ n) := by
  have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hn
  have h2 := Nat.one_le_two_pow (n := n)
  have hs : (1#64 <<< n).toNat = 2 ^ n := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have ha : (18446744073709551615#64 &&& 1#64 <<< n) = 1#64 <<< n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hs, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl, Nat.and_comm,
      Nat.and_two_pow_sub_one_of_lt_two_pow h1]
  have hm : ((18446744073709551615#64 &&& 1#64 <<< n) - 1#64).toNat = 2 ^ n - 1 := by
    rw [ha, BitVec.toNat_sub, hs]; simp only [BitVec.toNat_ofNat]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hm, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk)]

theorem val_small (X n : Nat) (hn : n ≤ 64) : val X n = Exp.newton (min 64 n) (X % Exp.B) % 2 ^ n := by
  unfold val Exp.modularInverseModPowerOfTwo; rw [if_pos hn]

set_option maxRecDepth 20000 in
/-- the post when only the window and possibly `z`'s array were written, `z` kept (`L' = L`, `b' = b + stkR H s.mem st`:
the reserve is refunded, the capacity unchanged) -/
theorem post_keep {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (zr : List (Nat × Nat))
    (hzr : zr = [] ∨ (0 < zc ∧ zr = [(zp, zp + 8 * zc)])) (s' : State)
    (hF : MemFrame s.mem s'.mem (win s (K kc) A ++ zr))
    (hinv : R.inv (b + stkR H s.mem st) L (s.regs 14).toNat (view R.rt L s'.mem))
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    {l' : Nat} (e0 : (s'.regs 0).toNat = zp) (e1 : (s'.regs 3).toNat = l') (e2 : (s'.regs 1).toNat = zc)
    (hv : natVal s'.mem zp l' = val (natVal s.mem xp xl) n) (hn : NatNorm s'.mem zp l') (hlc : l' ≤ zc) :
    Post R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, -, -, -, hLs, -, -⟩, -, -, -, -, -, -, -, ⟨hzc40, hzlive, -⟩, -, -, -, -, -, -, -, -, -,
    ⟨-, hst, hstw, -⟩, -, ⟨hsz, -, -⟩, -, -, -, -, -, -, -⟩ := hpre'
  have hFb : MemFrame s.mem s'.mem (R.rt ++ win s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) := by
    refine hF.mono fun a k h => ?_
    simp only [outside_append] at h ⊢
    refine ⟨h.1.1.2, ?_⟩
    rcases hzr with rfl | ⟨-, rfl⟩
    · simp
    · exact h.1.2
  have hst' : Outside st 24 (win s (K kc) A ++ zr) := by
    simp only [outside_append]
    refine ⟨hstw, ?_⟩
    rcases hzr with rfl | ⟨-, rfl⟩
    · simp
    · unfold Apart at hsz; simp only [outside_cons, outside_nil, and_true]; omega
  obtain ⟨-, w0, -, w2⟩ := stkOK_frame hst hF hst' (LiveExt.refl R L)
  refine ⟨hfs, hdf, zp, l', zc, e0, e1, e2, hv, hn, hlc, hzc40, L, b + stkR H s.mem st, LiveExt.refl R L,
    by dsimp only; rw [stkR_congr w2]; omega, hinv, ?_,
    Or.inl ⟨rfl, rfl⟩, ⟨stackBack_frame hst hF hst' (LiveExt.refl R L), fun hn => absurd ⟨w0, w2⟩ hn⟩, hFb, ?_,
    fun _ hn => absurd ⟨w0, w2⟩ hn⟩
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hzlive hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · refine Expmc.liveFrame_of_frame hF fun a k hin hws => ?_
    simp only [outside_append] at hws ⊢
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr, h1, h2⟩ := hin
      have := hLs r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · rcases hzr with rfl | ⟨-, rfl⟩
      · simp
      · exact hws.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `TESTQ R12, R12` at `+0x330` with `R12 = k0 mod 2^n` to the return -/
theorem small_tail (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat)
    (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State)
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hs : n ≤ 64) (S : State)
    (hpc : S.rip = BitVec.ofNat 64 0x5eabf0) (h4 : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224))
    (h5 : S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8)) (hab : Abi s S)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h12 : S.regs 12 = BitVec.ofNat 64 (k0 s xp xl n % 2 ^ n))
    (hF : MemFrame s.mem S.mem (win s (K kc) A)) (hfw : Fw0 s S.mem) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S := by
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  obtain ⟨f1, f2⟩ := hfw
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, -, -, -⟩, -, -, -, -, -, -, hzc0, ⟨-, hzlive, hzw⟩, -⟩ := hpre'
  have hinv0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [K, A, regSP] at hw hout hb' ha
  have hra := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hk0 : k0 s xp xl n < 2 ^ 64 := by
    unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
  have hvl : k0 s xp xl n % 2 ^ n < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk0
  have f2' : S.mem.readLE ((s.regs 4).toNat - 224 + 216) 8 = (s.regs 5).toNat := by
    rw [show (s.regs 4).toNat - 224 + 216 = (s.regs 4).toNat - 8 by omega]; exact f2
  have f1' : S.mem.readLE ((s.regs 4).toNat - 224 + 224) 8 < 140737488355328 := by
    rw [show (s.regs 4).toNat - 224 + 224 = (s.regs 4).toNat by omega, f1]; exact hra
  have f1r : S.mem.readLE ((s.regs 4).toNat - 224 + 224) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [show (s.regs 4).toNat - 224 + 224 = (s.regs 4).toNat by omega, f1]
  unfold Goal
  by_cases hv : k0 s xp xl n % 2 ^ n = 0
  · have hm0 : BitVec.ofNat 64 (k0 s xp xl n % 2 ^ n) = 0#64 := by rw [hv]
    janus64_run [hm0, f1r, f2', f1']
    refine ⟨?_, post_keep (l' := 0) hpre [] (Or.inl rfl) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _)⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals try janus64_simp
    all_goals first
      | (with_reducible exact hfs) | (with_reducible exact hdf)
      | (show MemFrame _ _ _; simpa using hF)
      | (exact FvModexp.Amd64.NatAdd.inv_win hF hout hb' hinv0)
      | (rw [val_small _ _ hs]; simp only [k0] at hv; rw [hv]; rfl)
      | (exact Or.inl rfl)
  · have hmz : ¬ BitVec.ofNat 64 (k0 s xp xl n % 2 ^ n) = 0#64 := by
      intro h; apply hv; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvl] at this; simpa using this
    have hz' : ¬ BitVec.ofNat 64 zc = 0#64 := by
      intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    obtain ⟨z8, zh, zacc, z48⟩ := hzlive (by omega)
    have hza : S.mem.accessible zp 8 true = true := by
      rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_sub _ zacc (Or.inr rfl) (Nat.le_refl _) (by omega)
    obtain ⟨hzo, -⟩ := hzw (by omega)
    simp only [win, outside_cons, outside_nil, and_true, K, A] at hzo
    have g1 : (S.mem.writeLE zp 8 (k0 s xp xl n % 2 ^ n)).readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact f1
    have g2 : (S.mem.writeLE zp 8 (k0 s xp xl n % 2 ^ n)).readLE ((s.regs 4).toNat - 224 + 216) 8 =
        (s.regs 5).toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact f2'
    have g1' : (S.mem.writeLE zp 8 (k0 s xp xl n % 2 ^ n)).readLE ((s.regs 4).toNat - 224 + 224) 8 < 140737488355328 := by
      rw [show (s.regs 4).toNat - 224 + 224 = (s.regs 4).toNat by omega, g1]; exact hra
    have g1r : (S.mem.writeLE zp 8 (k0 s xp xl n % 2 ^ n)).readLE ((s.regs 4).toNat - 224 + 224) 8 =
        s.mem.readLE (s.regs 4).toNat 8 := by
      rw [show (s.regs 4).toNat - 224 + 224 = (s.regs 4).toNat by omega, g1]
    janus64_run [hmz, hz', g1r, g2, Nat.mod_eq_of_lt hvl, g1']
    have hzh : Held R L zp 8 := zh.sub (Nat.le_refl _) (by omega)
    refine ⟨?_, post_keep (l' := 1) hpre [(zp, zp + 8 * zc)] (Or.inr ⟨by omega, rfl⟩) _ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ (by omega)⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals try janus64_simp
    all_goals first
      | (with_reducible exact hfs) | (with_reducible exact hdf)
      | (show MemFrame _ _ _
         refine MemFrame.writeLE_inRanges (hF.mono fun a k h => ?_) _ ⟨(zp, zp + 8 * zc), by simp, by omega, by omega⟩
         simp only [outside_append] at h; exact h.1)
      | (exact inv_store_held (FvModexp.Amd64.NatAdd.inv_win hF hout hb' hinv0) hzh)
      | (show NatNorm _ _ _
         refine Or.inr ?_
         show Janus.Arm64.Memory.readLE _ (zp + 8 * (1 - 1)) 8 ≠ 0
         rw [show zp + 8 * (1 - 1) = zp by omega, Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt hvl]
         exact hv)
      | (rw [val_small _ _ hs])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem small (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) :
    JS impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s := by
  intro S hpre hs hpc ⟨h4, h5, hab, h0, h1, h7, h6, h8, h9, h10, h12, hF, hrg, hfw, r8, r40⟩
  have hn1 : 1 ≤ n := hpre.2.2.2.1
  have hk0 : k0 s xp xl n < 2 ^ 64 := by
    unfold k0 Exp.newton; rw [← Exp.B_def]; exact Exp.newton_lt _ _ _ _ (Nat.mod_lt _ Exp.B_pos)
  obtain ⟨a14, afs, ax15, adf⟩ := hab
  by_cases h64 : n = 64
  · subst h64
    have hm := mask64 _ hk0
    unfold Goal
    janus64_run [hs, hm] until [0x5eabf0]
    refine small_tail impl R kc H sqrC mulC b L zp zl zc st xp xl xc 64 s hpre hs _ rfl ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
      ?_ ?_
    all_goals try janus64_simp
    all_goals first | (with_reducible exact hF) | (with_reducible exact hfw) | (with_reducible exact afs) | (with_reducible exact ax15) | (with_reducible exact adf) | (with_reducible exact a14) | skip
  · have hlt : n < 64 := by omega
    have hmod : n % 64 = n := Nat.mod_eq_of_lt hlt
    have hne : ¬ n = 0 := by omega
    have hm := maskLt _ _ hk0 hlt
    unfold Goal
    janus64_run [hs, hlt, hmod, hne, hm] until [0x5eabf0]
    refine small_tail impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s hpre hs _ rfl ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
      ?_ ?_
    all_goals try janus64_simp
    all_goals first | (with_reducible exact hF) | (with_reducible exact hfw) | (with_reducible exact afs) | (with_reducible exact ax15) | (with_reducible exact adf) | (with_reducible exact a14) | skip

end FvModexp.Amd64.ModInv
