import FvModexp.Proofs.Amd64.Int.ModMA
import FvModexp.Proofs.Amd64.Int.ModQP
import FvModexp.Proofs.Amd64.Int.QRFun

set_option autoImplicit false

/-!
# `(*Int).Mod` (amd64): `z.Mod(z, y)` returns `z = z mod y` (`ModSpecA` = `RunIface.ModSpec` + `hasADX` readable)

Composition: segment A (`runMA`: entry → `QuoRem`'s entry on the non-alias path; `QRPre` by `qrPre_of`), the call of
`QuoRem` (premise `QRSpec`, an `Ensures` on `LibQR`, moved to `LibMod` by `Ensures.toSummaryIn`), segment B (`runMB`:
`z.neg = 0` → `RET`) and `intPost_lift`.

`ModSpecA` is `RunIface.ModSpec` with one more precondition conjunct, `s.mem.accessible Callees.adxAddr 1 false = true`:
since asm s48 every amd64 `nat.div` precondition (here `IMod.DivPreM`) requires `hasADX` readable, and `ModSpec`'s
precondition does not provide it (INTERFACE NOTE for top: the Run row discharges it from its region facts, as for
`ExpHyp.DivPre`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe maxW ModBudget lenW PoolG ModX namesMod)

/-- **`z.Mod(z, y)`** (amd64) as `Run` calls it: `RunIface.ModSpec` with `hasADX` readable in the precondition -/
def ModSpecA (impl : List Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesMod).link impl) (segAddr Extracted.program (RunIface.P ++ "(*Int).Mod"))
      [z, z, y]
      (fun s => (IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above) ∧
        ModX s.mem z.toNat) ∧ s.mem.accessible Callees.adxAddr 1 false = true)
      (fun s s' => s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
        IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

theorem namesMod_eq : namesMod = LibMod.names := by decide

theorem qr_sub : ∀ x, LibQR.names.contains x = true → LibMod.names.contains x = true :=
  Callees.sub_of_all (by decide)

set_option maxRecDepth 20000 in
/-- the return address of `Mod`'s `QuoRem` call (`Mod+0x217`) is outside `LibQR` -/
theorem raM_ret (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments LibQR.names).link impl) raM := by
  have := retAddr_restrict hap (cs := Extracted.seg3) (ns := LibQR.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 0x217
    (by decide) (by decide)
  rwa [show Extracted.seg3.base + 0x217 = raM by decide] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).Mod`** (amd64): `ModSpecA` from `QuoRem`'s summary as `Mod` calls it (`QRSpec`, window `stkQ`, 128) -/
theorem mod_ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {stkQ : Nat} (hQ : QRSpec impl R stkQ 128) {stk above : Nat} (hstk : stkQ + 168 ≤ stk) (hQ8 : 8 ≤ stkQ)
    (hab : 16 ≤ above) :
    ModSpecA impl R stk above := by
  intro b L z y
  rw [namesMod_eq, ← LibMod.eq_only, fnM_eq]
  intro ret hret s hs hpre
  janus64_intro hs
  have hr48 := hret.user
  obtain ⟨⟨hIP, hyv, hlz, hly, hpool, hX⟩, hadx⟩ := hpre
  have hIP' := hIP
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hstk0, hab48, hacc⟩, hal, -, hrt, -, -, hLs, -⟩, -, -, -, -, hops, hpw⟩ := hIP'
  simp only [regSP, regG, stackguard0, stackguard0Offset] at hstk0 hab48 hacc hg1 hg2 hg3
  have hoz := hops z.toNat (by simp)
  have hoy := hops y.toNat (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hpw
  obtain ⟨⟨hzyH, -, -, hzyArr⟩, -⟩ := hpw
  obtain ⟨⟨-, -, hz48, hzacc, -, hzL, -, -, -, -⟩, hzW, hzO, -, -, -, -⟩ := hoz
  obtain ⟨⟨-, -, hy48, hyacc, -, hyL, -, -, -, -⟩, hyW, hyO, -, -, -, -⟩ := hoy
  generalize hzp : s.mem.readLE (z.toNat + 8) 8 = zp at hzL hzyArr hzO
  generalize hzc : s.mem.readLE (z.toNat + 24) 8 = zc at hzL hzyArr hzO
  generalize hyp : s.mem.readLE (y.toNat + 8) 8 = yp at hyL hzyArr hyO
  generalize hyc : s.mem.readLE (y.toNat + 24) 8 = yc at hyL hzyArr hyO
  have hali : zc = 0 ∨ yc = 0 ∨ (zp + 8 * zc) % 2 ^ 64 ≠ (yp + 8 * yc) % 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos zc with h1 | h1
    · exact Or.inl h1
    rcases Nat.eq_zero_or_pos yc with h2 | h2
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    have ha := hzyArr h1 h2; unfold Apart at ha
    have hz' := (hzL h1).2.2.2; have hy' := (hyL h2).2.2.2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  generalize ht : (s.regs 4).toNat = t at hstk0 hab48 hacc hg3 hal
  have hsp0 : s.regs 4 = BitVec.ofNat 64 t := by rw [← ht, Expmc.bv_ofNat_toNat]
  have hzS : z.toNat + 32 ≤ t - stk ∨ t + above ≤ z.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hzW; omega
  have hyS : y.toNat + 32 ≤ t - stk ∨ t + above ≤ y.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hyW; omega
  unfold Apart at hzyH
  -- segment A
  refine returns_of_reaches (runMA impl ret hret _ t (s.regs 14).toNat (s.regs 5).toNat z.toNat y.toNat
    zp zc yp yc s.mem (BitVec.isLt _) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hz48
    (Janus.Arm64.Memory.accessible_weaken _ hzacc) hy48 (Janus.Arm64.Memory.accessible_weaken _ hyacc)
    (by omega) (by omega) (by omega) hzp hzc hyp hyc hali
    s h_rip hsp0 (h_a0.trans (Expmc.bv_ofNat_toNat _).symm) (h_a1.trans (Expmc.bv_ofNat_toNat _).symm)
    (h_a2.trans (Expmc.bv_ofNat_toNat _).symm) (Expmc.bv_ofNat_toNat _).symm (Expmc.bv_ofNat_toNat _).symm h_x15 rfl
    ?KA)
  intro SQ MQ c_pc c_sp c0 c3 c1 c7 c14 c5 cfs cdf cx cm hF hrg r_ra q8 q16 q24 rbp r8
  subst cm
  have hspQ : (SQ.regs 4).toNat = (s.regs 4).toNat - 168 := by rw [c_sp, BitVec.toNat_ofNat, ht]; omega
  have hF' : MemFrame s.mem SQ.mem [((s.regs 4).toNat - 168, (s.regs 4).toNat - 160),
      ((s.regs 4).toNat - 88, (s.regs 4).toNat - 40), ((s.regs 4).toNat - 8, (s.regs 4).toNat),
      ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := by rw [ht]; exact hF
  have hP := qrPre_of hIP hyv hlz hly hpool hX hadx hstk hab hspQ c14 cfs hrg hF' (by rw [ht]; exact q8)
    (by rw [ht]; exact q16) (by rw [ht]; exact q24)
  rw [ht] at hP
  -- the call of `QuoRem`
  have hS := Ensures.toSummaryIn (hQ b L (BitVec.ofNat 64 (t - 72)) z y) (A64.noExit_restrict64 hap LibQR.names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap qr_sub)
  rw [← LibMod.eq_only, fnQ_eq] at hS
  simp only [bv_toNat (show t - 72 < 2 ^ 64 by omega)] at hS
  refine Reaches.call_regions (hS.withExit hret) c_pc ⟨?_, cx.trans h_x15, ?_, cdf.trans h_df, hP⟩
    fun S5 hpc5 hq hrg5 => ?_
  · rw [c_sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), r_ra]; exact raM_ret impl hap
  · simp [ArgsFrom64, argReg, intArgRegs, c0, c3, c1, c7]
  obtain ⟨⟨sp5, rbp5, r14_5, x15_5⟩, hfs5, hdf5, h05, hPost, hyv5⟩ := hq
  have hPost' := hPost
  obtain ⟨-, L', b', -, -, -, hokz, -, hMF5, -⟩ := hPost'
  have hFw : MemFrame s.mem SQ.mem (win s stk above) := hF'.mono fun a k h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega
  -- what `QuoRem` keeps: `[t - 8, t + 16)` (above its window, outside `R.rt`, `z`'s header and array)
  have hkeep : ∀ a k, t - 8 ≤ a → a + k ≤ t + 16 → S5.mem.readLE a k = SQ.mem.readLE a k := by
    intro a k h1 h2
    refine hMF5.readLE a k ?_
    have hzw' : Outside a k [(z.toNat, z.toNat + 32)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    have hza' : Outside a k (RunIface.arrW SQ.mem z.toNat) := by
      simp only [RunIface.arrW]
      rw [hFw.readLE _ _ (hzW.of_sub (by omega) (by omega)), hFw.readLE _ _ (hzW.of_sub (by omega) (by omega)),
        hzp, hzc]
      split
      · rename_i hc
        have := hzO hc; simp only [win, ht, outside_cons, outside_nil, and_true] at this
        simp only [outside_cons, outside_nil, and_true]; omega
      · exact trivial
    rw [outside_append, outside_append, outside_cons]
    refine ⟨⟨(hrt.of_sub (by rw [ht]; omega) (by rw [ht]; omega) : Outside a k R.rt), ?_⟩, ?_, hza'⟩
    · simp only [win, hspQ, ht, outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true] at hzw'; exact hzw'
  have hsp5 : S5.regs 4 = BitVec.ofNat 64 (t - 160) := by
    have e : (S5.regs 4).toNat = ((SQ.regs 4).toNat + 8) % 2 ^ 64 := by rw [sp5, BitVec.toNat_add]; rfl
    apply BitVec.eq_of_toNat_eq
    rw [e, hspQ, ht, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have sra : S5.mem.readLE t 8 = ret := by
    rw [hkeep _ _ (by omega) (by omega), hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← ht]
    exact h_ret
  -- segment B
  refine runMB impl ret hret _ t (s.regs 5).toNat z.toNat (by omega) (by omega) (by omega) S5
    (by rw [hMF5.accessible, hF.accessible]; exact (Janus.Arm64.Memory.accessible_weaken _
          (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))))
    (Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hokz.2.2.2.1 (by omega) (by omega)))
    (by rw [hpc5, retAddrOf, c_sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), r_ra]) hsp5
    (by rw [hkeep _ _ (by omega) (by omega)]; exact r8) (by rw [hkeep _ _ (by omega) (by omega)]; exact rbp) sra
    hokz.1 ?KB
  intro s6 hm6 hsp6 h06 h56 h146 hfs6 hdf6 hx6
  -- `QuoRem`'s view of `z`, `y` is `Mod`'s
  have hz : ∀ o, o + 8 ≤ 32 → SQ.mem.readLE (z.toNat + o) 8 = s.mem.readLE (z.toNat + o) 8 := fun o ho =>
    hFw.readLE _ _ (hzW.of_sub (by omega) (by omega))
  have hy : ∀ o, o + 8 ≤ 32 → SQ.mem.readLE (y.toNat + o) 8 = s.mem.readLE (y.toNat + o) 8 := fun o ho =>
    hFw.readLE _ _ (hyW.of_sub (by omega) (by omega))
  have hvz : IntV SQ.mem z.toNat = IntV s.mem z.toNat := by
    simp only [IntV]; rw [hz 8 (by omega), hz 16 (by omega)]
    refine natVal_frame' hFw fun h => ?_
    have hlc := (hIP.2.2.2.2.2.1 z.toNat (by simp)).1.2.2.2.2.2.2.1
    rw [hzc] at hlc; rw [hzp]
    exact (hzO (by omega)).of_sub (Nat.le_refl _) (by omega)
  have hvy : IntV SQ.mem y.toNat = IntV s.mem y.toNat := by
    simp only [IntV]; rw [hy 8 (by omega), hy 16 (by omega)]
    refine natVal_frame' hFw fun h => ?_
    have hlc := (hIP.2.2.2.2.2.1 y.toNat (by simp)).1.2.2.2.2.2.2.1
    rw [hyc] at hlc; rw [hyp]
    exact (hyO (by omega)).of_sub (Nat.le_refl _) (by omega)
  have hlen : lenW SQ.mem z.toNat = lenW s.mem z.toNat ∧ lenW SQ.mem y.toNat = lenW s.mem y.toNat := by
    simp only [lenW]; exact ⟨hz 16 (by omega), hy 16 (by omega)⟩
  rw [hlen.1, hlen.2, hvz, hvy] at hPost
  rw [hvy] at hyv5
  have hP6 : IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stkQ 128 z.toNat
      (IntV s.mem z.toNat % IntV s.mem y.toNat) SQ s6 := by
    unfold IntPost at hPost ⊢; rw [hm6]; exact hPost
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfs6.trans (hfs5.trans cfs), hdf6.trans (hdf5.trans cdf),
    h06.trans (Expmc.bv_ofNat_toNat _), intPost_lift hP6 hFw hLs hzW (fun a n h => by
      simp only [win, hspQ, outside_cons, outside_nil, and_true] at h ⊢; omega) c14,
    by rw [hm6]; exact hyv5⟩
  · show s6.regs 4 = s.regs 4 + 8#64
    rw [hsp6, hsp0]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · show s6.regs 5 = s.regs 5
    rw [h56, Expmc.bv_ofNat_toNat]
  · show s6.regs 14 = s.regs 14
    rw [h146, r14_5, c14]
  · show s6.xmm 15 = s.xmm 15
    rw [hx6, x15_5, cx]

/-- **`(*Int).Mod`** (amd64), `ModSpecA` from `nat.div` as `QuoRem` calls it (`DivHypM`; with top's
`NatQ/DivMFull.ensML`: `nsD = LibDiv.names`, `stkD = 41512`, `aboveD = 112`, so `stk ≥ 41800`), the 4-slot write
barrier and `div`'s cost within `ModBudget` -/
theorem mod_ensD (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {nsD : List String} {stkD aboveD : Nat} {cost : Nat → Nat → Nat}
    (hD : DivHypM impl R nsD stkD aboveD cost)
    (hnsD : ∀ x, nsD.contains x = true → LibQR.names.contains x = true)
    (hnsQ : nsD.contains Extracted.seg6.name = false)
    (hwb : WbLiveContract64 (LibQR.program.link impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    {stk above : Nat} (hstk : stkD + 288 ≤ stk) (h4392 : 4392 ≤ stk) (habD : aboveD ≤ 112) (hab : 16 ≤ above)
    (hbud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → cost ul vl ≤ ModBudget (max ul vl)) :
    ModSpecA impl R stk above :=
  mod_ens impl hap R (stkQ := stk - 168)
    (qr_ens impl hap R hD hnsD hnsQ hwb (by omega) habD (by omega) (Nat.le_refl _) hbud) (by omega) (by omega) hab

end FvModexp.Amd64.IMod
