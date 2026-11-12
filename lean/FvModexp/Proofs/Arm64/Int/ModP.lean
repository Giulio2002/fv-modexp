import FvModexp.Proofs.Arm64.Int.ModLem

/-!
# `(*Int).Mod` (arm64): `nat.div`'s precondition `DivPreM` at its entry from `ModSpecX`'s precondition (pure)

At `nat.div`'s entry (`SP = t - 304`, `t` = Mod's entry `SP`) the memory differs from the entry memory only in
`[t - 312, t - 8) ∪ [t + 8, t + 16)` (Mod's and QuoRem's frames). `u = z.abs = (zp, zl, zc)`, `v = y.abs = (yp, yl, yc)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IMod

open FvModexp.Arm64.RunIface (IntOK IntPre IntV PoolG)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem divPre_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA : Nat}
    (hIP : IntPre R b B L stk above [zA, yA] s) (hyv : 0 < IntV s.mem yA)
    (hpool : PoolG R s.mem (win s stk above)) (hX : ModX s.mem zA)
    {stkD aboveD : Nat} (hstkD : stkD + 304 ≤ stk) (h312 : 312 ≤ stk) (habD : aboveD ≤ 120) (hab : 32 ≤ above)
    {zp zl zc yp yl yc : Nat}
    (hzp : s.mem.readLE (zA + 8) 8 = zp) (hzl : s.mem.readLE (zA + 16) 8 = zl) (hzc : s.mem.readLE (zA + 24) 8 = zc)
    (hyp : s.mem.readLE (yA + 8) 8 = yp) (hyl : s.mem.readLE (yA + 16) 8 = yl) (hyc : s.mem.readLE (yA + 24) 8 = yc)
    (hlz : zl ≤ 128) (hly : yl ≤ 128)
    {cost : Nat → Nat → Nat} (hcost : cost zl yl ≤ B)
    {S3 : State} (hsp : S3.sp.toNat = s.sp.toNat - 304) (h28 : S3.regs 28 = s.regs 28)
    (hrg : S3.mem.regions = s.mem.regions)
    (hF : MemFrame s.mem S3.mem [(s.sp.toNat - 312, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]) :
    DivPreM R b cost L stkD aboveD zp zl zc yp yl S3 := by
  obtain ⟨hce, hsv, hG, hBb, hinv, hops, hpw⟩ := hIP
  have hce' := hce
  obtain ⟨-, ⟨-, hst, -, -⟩, -, hrt, -, -, hLs, -⟩ := hce'
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hpw
  obtain ⟨⟨-, -, -, hzyA⟩, -⟩ := hpw
  obtain ⟨⟨-, -, -, -, -, hzL, hzlc, hzN, -, hzc40⟩, -, hzO, -, hzG⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, hyL, hylc, hyN, -, hyc40⟩, -, hyO, -, hyG⟩ := hoy
  unfold ModX at hX
  rw [hzp, hzc] at hzL hzO hzG hzyA hX
  rw [hzl, hzc] at hzlc
  rw [hzp, hzl] at hzN
  rw [hyp, hyc] at hyL hyO hyG hzyA
  rw [hyl, hyc] at hylc
  rw [hyp, hyl] at hyN
  have hyv' : 0 < natVal s.mem yp yl := by simp only [IntV] at hyv; rw [hyp, hyl] at hyv; exact hyv
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp only [natVal_zero] at hyv'; omega
    · exact h
  have hyc0 : 0 < yc := by omega
  have hst' : stk ≤ s.sp.toNat := hst
  have hFw : MemFrame s.mem S3.mem (R.rt ++ winA s stk above) := hF.mono fun a k h => by
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hac : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  -- window of the callee ⊆ the caller's
  have hwin : ∀ a n, Outside a n (win s stk above) → Outside a n (win S3 stkD aboveD) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hfr : ∀ a n, Outside a n (win s stk above) →
      Outside a n [(s.sp.toNat - 312, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)] := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hg : (S3.regs 28).toNat = (s.regs 28).toNat := by rw [h28]
  have hzH : 0 < zc → Held R L zp (8 * zc) := fun h => (hzL h).2.1
  have hzacc : 0 < zc → s.mem.accessible zp (8 * zc) true = true := fun h => (hzL h).2.2.1
  have hz48 : 0 < zc → zp + 8 * zc ≤ 2 ^ 48 := fun h => (hzL h).2.2.2
  obtain ⟨-, hyH, hyacc, hy48⟩ := hyL hyc0
  refine ⟨callEnv_shift hce hLs hFw hsp h28 hrg (by omega) (by omega) (by omega) (by decide), hsv,
    globals_shift hG hFw (fun a n h => by
      simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega) hwin, hzlc, ⟨by omega, natLive_frame hzL hac, fun h => ?_⟩,
    ⟨by omega, fun h => ?_⟩, ?_, by omega, hyl0, by omega, natNorm_frame hF ?_ hzN, natNorm_frame hF ?_ hyN,
    fun h => ⟨?_, hX h⟩, ?_, by omega, ?_⟩
  · exact ⟨hwin _ _ (hzO h), by rw [hg]; exact hzG h⟩
  · refine ⟨by omega, by rw [hac]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ (hzacc (by omega))
      (Nat.le_refl _) (by omega)), by have := hz48 (by omega); omega, (hzH (by omega)).sub (Nat.le_refl _) (by omega),
      (hwin _ _ (hzO (by omega))).of_sub (Nat.le_refl _) (by omega)⟩
  · exact ⟨by omega, by rw [hac]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hyacc
      (Nat.le_refl _) (by omega)), by omega, hyH.sub (Nat.le_refl _) (by omega),
      (hwin _ _ (hyO hyc0)).of_sub (Nat.le_refl _) (by omega)⟩
  · intro h; exact (hfr _ _ (hzO (by omega))).of_sub (Nat.le_refl _) (by omega)
  · intro h; exact (hfr _ _ (hyO hyc0)).of_sub (Nat.le_refl _) (by omega)
  · have := hzyA h hyc0; unfold Apart at this ⊢; omega
  · obtain ⟨h0, hrd, hprt, hpw'⟩ := hpool
    refine ⟨h0, ?_, hprt, hwin _ _ hpw'⟩
    rw [hF.readLE _ _ (hfr _ _ hpw')]; exact hrd
  · rw [hg]; exact Expmc.inv_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (hrt.of_sub (by omega) (by simp only; omega))
      · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))) hinv

end FvModexp.Arm64.IMod
