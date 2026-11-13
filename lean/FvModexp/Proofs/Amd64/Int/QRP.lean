import FvModexp.Proofs.Amd64.Int.QRLem
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64): `nat.div`'s precondition `DivPreM` at its entry from `QRPre` (pure)

At `nat.div`'s entry (`RSP = t - 120`, `t` = `QuoRem`'s entry `RSP`) the memory differs from the entry memory only in
`[t - 120, t - 64) ∪ [t - 8, t) ∪ [t + 8, t + 40)` (segment A's stores). `u = z.abs = (zp, zl, zc)`, `v = y.abs =
(yp, yl, yc)`, both as stack arguments at `RSP + 8 … + 48`. Twin of the arm64 `IMod.divPre_of` (Arm64/Int/ModP.lean).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntOK IntPre IntV PoolG ModX)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem divPre_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA : Nat}
    (hIP : IntPre R b B L stk above [zA, yA] s) (hyv : 0 < IntV s.mem yA)
    (hpool : PoolG R s.mem (win s stk above)) (hX : ModX s.mem zA)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true)
    {stkD aboveD : Nat} (hstkD : stkD + 120 ≤ stk) (habD : aboveD ≤ 112) (hab : 40 ≤ above)
    {zp zl zc yp yl yc : Nat}
    (hzp : s.mem.readLE (zA + 8) 8 = zp) (hzl : s.mem.readLE (zA + 16) 8 = zl) (hzc : s.mem.readLE (zA + 24) 8 = zc)
    (hyp : s.mem.readLE (yA + 8) 8 = yp) (hyl : s.mem.readLE (yA + 16) 8 = yl) (hyc : s.mem.readLE (yA + 24) 8 = yc)
    (hlz : zl ≤ 128) (hly : yl ≤ 128)
    {cost : Nat → Nat → Nat} (hcost : cost zl yl ≤ B)
    {S3 : State} (hsp : (S3.regs 4).toNat = (s.regs 4).toNat - 120) (h14 : S3.regs 14 = s.regs 14)
    (hfs : S3.fsBase = s.fsBase) (hrg : S3.mem.regions = s.mem.regions)
    (hF : MemFrame s.mem S3.mem [((s.regs 4).toNat - 120, (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 40)])
    (a8 : S3.mem.readLE ((S3.regs 4).toNat + 8) 8 = zp) (a16 : S3.mem.readLE ((S3.regs 4).toNat + 16) 8 = zl)
    (a24 : S3.mem.readLE ((S3.regs 4).toNat + 24) 8 = zc) (a32 : S3.mem.readLE ((S3.regs 4).toNat + 32) 8 = yp)
    (a40 : S3.mem.readLE ((S3.regs 4).toNat + 40) 8 = yl) (a48 : S3.mem.readLE ((S3.regs 4).toNat + 48) 8 = yc) :
    DivPreM R b cost L stkD aboveD zp zl zc yp yl yc S3 := by
  obtain ⟨hce, hsv, hG, hBb, hinv, hops, hpw⟩ := hIP
  have hce' := hce
  obtain ⟨-, ⟨hst, -, -⟩, -, -, hrt, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hst
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hpw
  obtain ⟨⟨-, -, -, hzyA⟩, -⟩ := hpw
  obtain ⟨⟨-, -, -, -, -, hzL, hzlc, hzN, -, hzc40⟩, -, hzO, -, hzG, -, hzT⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, hyL, hylc, hyN, -, hyc40⟩, -, hyO, -, hyG, -, hyT⟩ := hoy
  unfold ModX at hX
  rw [hzp, hzc] at hzL hzO hzG hzT hzyA hX
  rw [hzl, hzc] at hzlc
  rw [hzp, hzl] at hzN
  rw [hyp, hyc] at hyL hyO hyG hyT hzyA
  rw [hyl, hyc] at hylc
  rw [hyp, hyl] at hyN
  rw [hzc] at hzc40
  rw [hyc] at hyc40
  have hyv' : 0 < natVal s.mem yp yl := by simp only [IntV] at hyv; rw [hyp, hyl] at hyv; exact hyv
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp only [natVal_zero] at hyv'; omega
    · exact h
  have hyc0 : 0 < yc := by omega
  have hFw : MemFrame s.mem S3.mem (R.rt ++ win s stk above) := hF.mono fun a k h => by
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hac : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  -- window of the callee ⊆ the caller's
  have hwin : ∀ a n, Outside a n (win s stk above) → Outside a n (win S3 stkD aboveD) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hfr : ∀ a n, Outside a n (win s stk above) →
      Outside a n [((s.regs 4).toNat - 120, (s.regs 4).toNat - 64),
        ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 40)] := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hg : (S3.regs 14).toNat = (s.regs 14).toNat := by rw [h14]
  have hzH : 0 < zc → Held R L zp (8 * zc) := fun h => (hzL h).2.1
  have hzacc : 0 < zc → s.mem.accessible zp (8 * zc) true = true := fun h => (hzL h).2.2.1
  have hz48 : 0 < zc → zp + 8 * zc ≤ 2 ^ 48 := fun h => (hzL h).2.2.2
  obtain ⟨-, hyH, hyacc, hy48⟩ := hyL hyc0
  refine ⟨a8, a16, a24, a32, a40, a48,
    callEnv_shift hce hLs hFw hsp h14 hfs hrg (by omega) (by omega) (by decide), hsv,
    globals_win hG hF (by
      have := hG.2.2.2.2.2.2.2.2.2.1; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega) hwin,
    hzlc, ⟨by omega, natLive_frame hzL hac, fun h => ?_⟩,
    ⟨by omega, fun h => ?_⟩, ?_, by omega, hyl0, by omega, natNorm_frame hF ?_ hzN, natNorm_frame hF ?_ hyN,
    fun h => ⟨?_, hX h⟩, ?_, by omega, by rw [hac]; exact hadx, ?_⟩
  · exact ⟨hwin _ _ (hzO h), by rw [hg]; exact hzG h, by rw [hfs]; exact hzT h⟩
  · have e1 : S3.mem.accessible zp (8 * zl) false = true := by
      rw [hac]; exact Janus.Arm64.Memory.accessible_weaken _
        (Janus.Arm64.Memory.accessible_mono _ (hzacc (by omega)) (Nat.le_refl _) (by omega))
    exact ⟨by omega, e1, by have := hz48 (by omega); omega, (hzH (by omega)).sub (Nat.le_refl _) (by omega),
      (hwin _ _ (hzO (by omega))).of_sub (Nat.le_refl _) (by omega)⟩
  · have e1 : S3.mem.accessible yp (8 * yl) false = true := by
      rw [hac]; exact Janus.Arm64.Memory.accessible_weaken _
        (Janus.Arm64.Memory.accessible_mono _ hyacc (Nat.le_refl _) (by omega))
    exact ⟨by omega, e1, by omega, hyH.sub (Nat.le_refl _) (by omega),
      (hwin _ _ (hyO hyc0)).of_sub (Nat.le_refl _) (by omega)⟩
  · intro h; exact (hfr _ _ (hzO (by omega))).of_sub (Nat.le_refl _) (by omega)
  · intro h; exact (hfr _ _ (hyO hyc0)).of_sub (Nat.le_refl _) (by omega)
  · have := hzyA h hyc0; unfold Apart at this ⊢; omega
  · obtain ⟨h0, hrd, hprt, hpw'⟩ := hpool
    refine ⟨h0, ?_, hprt, hwin _ _ hpw'⟩
    rw [hF.readLE _ _ (hfr _ _ hpw')]; exact hrd
  · rw [hg]; exact Expmc.inv_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inr (hrt.of_sub (by omega) (by simp only; omega))
      · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))
      · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))) hinv

end FvModexp.Amd64.IMod
