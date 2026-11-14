import FvModexp.Proofs.Arm64.Nat.DrsSegD
/-!
# `divRecursiveStep` (arm64), final block after the correction loop: `qhatv.cmp(u.norm())` (natdiv.go:880)
`d2F`: from `d1F`'s call state → `nat.cmp` (`csumD`) → its return `0x1bac10` with `X0 = cmpQ |PF| st` (as
`BitVec.ofInt`), `McF`/`V3F` kept. Adapted from DrsD2.
-/
set_option autoImplicit false
set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the `nat.cmp` after the correction loop**, from `d1`'s call state -/
theorem d2F (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (c : Cx) (s : State)
    (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop)
    (X : State) (n' : Nat) (hpc : X.pc = BitVec.ofNat 64 cmpA) (hsp : X.sp = s.sp - 400#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rFD2) (h0 : X.regs 0 = BitVec.ofNat 64 qv)
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.PF s U).length) (h2 : X.regs 2 = BitVec.ofNat 64 (3 * c.vl))
    (h3 : X.regs 3 = BitVec.ofNat 64 c.up) (h4 : X.regs 4 = BitVec.ofNat 64 n')
    (hmc : McF R c s Lk bk X.mem j Z U qv st) (hv4 : V3F c s X.mem qv (c.PF s U).length) (hle : n' ≤ c.u1)
    (hv : natVal X.mem c.up n' = natVal X.mem c.up c.u1) (hN : NatNorm X.mem c.up n')
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rFD2 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 →
      T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.PF s U).length st) →
      McF R c s Lk bk T.mem j Z U qv st → V3F c s T.mem qv (c.PF s U).length →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, -, huw, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjB := hmc.jB
  have h40 := hcr.h40
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 24 40 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨⟨g1, g2, g3⟩, hsk, -, hout, -, -, hLs, -⟩ := hce'
  have hPl : (c.PF s U).length ≤ 3 * c.vl := by
    have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
      ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
    rw [Mdl.length_toL, List.length_take] at h1
    have h2 := qF_len (c := c) (s := s) (U := U)
    have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
    show (Mdl.norm _).length ≤ _
    rw [List.length_take]
    omega
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hqw := hmc.rg.w
  simp only [win, outside_cons, outside_nil, and_true] at hqw huw
  have huacc : X.mem.accessible c.up (8 * n') false = true := by
    rw [hmc.ev.fr.accessible]
    exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hua (by omega)
      (by omega))
  have t0 : (BitVec.ofNat 64 qv).toNat = qv := by rw [BitVec.toNat_ofNat]; omega
  have t1 : (BitVec.ofNat 64 (c.PF s U).length).toNat = (c.PF s U).length := by rw [BitVec.toNat_ofNat]; omega
  have t3 : (BitVec.ofNat 64 c.up).toNat = c.up := by
    rw [BitVec.toNat_ofNat]; omega
  have t4 : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; omega
  have hpre : CmpSum.Pre X := by
    unfold CmpSum.Pre GuardOK CmpSum.SliceOK
    rw [h30, h0, h1, h3, h4, t0, t1, t3, t4]
    refine ⟨by decide, by decide, ⟨g1, g2, by omega⟩, hsk, ?_, ?_⟩
    · by_cases hz : (c.PF s U).length = 0
      · exact Or.inl hz
      · refine Or.inr ⟨Memory.accessible_read_of_write _ (Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega)), ?_⟩
        unfold Apart; omega
    · by_cases hz : n' = 0
      · exact Or.inl hz
      · refine Or.inr ⟨huacc, ?_⟩
        unfold Apart; omega
  refine ReachesRet.call_regions (csumD impl hap) hpc hpre fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  have hfw : MemFrame X.mem m (winA X 24 40) := hf.mono fun x n ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hMF : MemFrame X.mem m (R.rt ++ winA X 24 40 ++ [(0, 0)]) := hfw.mono fun x n ho => by
    simp only [outside_append] at ho; exact ho.1.2
  have hLF : LiveFrame X.mem m Lk [(0, 0)] := lf_winX _ hfw hLs
  have hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m) := by
    rw [← h28]; exact inv_frame_winA hfw hout (by omega) (by omega) (by rw [h28]; exact hmc.ev.inv)
  have hreg' : m.regions = X.mem.regions := hrg
  -- the reads of `qhatv` and `uu` across the call
  have kQ : m.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) :=
    hfw.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have o0 : ∀ x n, Outside x n [(0, 0)] := fun x n => by simp only [outside_cons, outside_nil, and_true]; omega
  have a0 : ∀ x n, Apart x n 0 0 := fun x n => by unfold Apart; omega
  have rw' : ∀ x n, (x + n ≤ s.sp.toNat - 424 ∨ s.sp.toNat - 360 ≤ x) → m.readLE x n = X.mem.readLE x n :=
    fun x n h => hfw.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have ht0w := hcr.t0w
  simp only [win, outside_cons, outside_nil, and_true] at ht0w
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have hmcT : McF R c s Lk bk m j Z U qv st :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF (LiveExt.refl R Lk) hinv hreg' (Nat.le_refl _)
      (fun x n _ => o0 x n) (fun x n _ _ => o0 x n) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (a0 _ _) (a0 _ _) (a0 _ _) (a0 _ _)
      (by rw [limbs_congr (rw' _ _ (by omega))]; exact hmc.qk)
      (by rw [limbs_congr kQ]; exact hmc.bf)
      (by rw [limbs_congr (rw' _ _ (by omega))]; exact hmc.wk)
  -- the result
  have hlq : Asm.limbs X.mem qv (c.PF s U).length = st.buf.take (c.PF s U).length := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hPl]
  have hlu : Asm.limbs X.mem c.up n' = Mdl.norm st.w := Asm.limbs_norm hmc.wk hv hN
  have hres : CmpSum.cmpRes (c.PF s U).length n' (Asm.lv X.mem qv (c.PF s U).length) (Asm.lv X.mem c.up n') =
      BitVec.ofInt 64 (Mdl.cmpQ (c.PF s U).length st) := by
    refine (Asm.cmp_model X.mem qv c.up (c.PF s U).length n' _ rfl).trans ?_
    rw [hlq, hlu]; rfl
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ hmcT ⟨?_, ?_, ?_⟩
  · show X.regs 30 = _; exact h30
  · show X.sp = _; exact hsp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h29
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [h1, h4, h0, h3, t0, t1, t3, t4]; exact hres
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s320
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s144
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s160
end FvModexp.Arm64.DivRec
