import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsD2.lean)
# `divRecursiveStep` (amd64), after the correction loop: `qhatv.cmp(uu.norm())` (natdiv.go:844)

`d2`: from `d1`'s `CALL nat.cmp` state (callee entry, `RSP = r - 400`) → `nat.cmp` (`csumD`) → its return `0x5eff71`
with `RAX = cmpQ |P| stF` (`stF` = the model state after the correction loop), `Mc`/`V4` kept. Twin of `c2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the model state after the correction loop -/
@[reducible] def stF (c : Cx) (s : State) (j : Nat) (U : List Nat) : Mdl.St :=
  Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`nat.cmp` after the correction loop**, from `d1`'s call state -/
theorem d2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (c : Cx)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv : Nat)
    (hE : E R c s Lk bk S j Z U qv) (Q : State → Prop)
    (X : State) (n' : Nat) (hpc : X.rip = BitVec.ofNat 64 cmpA) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128) (h0 : X.regs 0 = BitVec.ofNat 64 qv)
    (h3 : X.regs 3 = BitVec.ofNat 64 (c.P s j U).length) (h1 : X.regs 1 = BitVec.ofNat 64 (3 * c.vl))
    (h7 : X.regs 7 = BitVec.ofNat 64 (c.uuP j)) (h6 : X.regs 6 = BitVec.ofNat 64 n')
    (hFR : MemFrame S.mem X.mem (isR s)) (hreg : X.mem.regions = S.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rD2) (hle : n' ≤ c.uuL j)
    (hv : natVal S.mem (c.uuP j) n' = natVal S.mem (c.uuP j) (c.uuL j)) (hN : NatNorm S.mem (c.uuP j) n')
    (k : ∀ T : State, T.rip = BitVec.ofNat 64 rD2 → T.regs 4 = s.regs 4 - 392#64 → T.regs 5 = s.regs 4 - 8#64 →
      T.regs 14 = s.regs 14 → T.fsBase = s.fsBase → T.df = false → T.xmm 15 = 0#128 →
      T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length (stF c s j U)) →
      Mc R c s Lk bk T.mem j Z U qv (stF c s j U) → V4 c s T.mem qv (c.P s j U).length →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hmc0 := hE.mc
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hua, hu48, -, huw, -⟩ := hpre.ua
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have h40 := hcr.h40
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame S.mem X.mem (is1 s) := hFR.mono fun x n ho => by
    simp only [isR, is1, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := Mc.own1 hmc0 hF1 hreg
  have hv4 := V4.own1 hE.v4 hF1 h0'
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 8 40 := Ev.callEnv hcr hmc.ev hspn h14 hfs (by omega) (by omega)
  obtain ⟨-, -, -, -, hout, -, -, hLs, -⟩ := hce'
  have hPl : (c.P s j U).length ≤ 3 * c.vl := by
    have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
      ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
    rw [Mdl.length_toL, List.length_take] at h1
    have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
    have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
    show (Mdl.norm _).length ≤ _
    rw [List.length_take]
    omega
  have hqa := hmc.qa
  have hq48 := Janus.Arm64.Memory.accessible_bound _ hqa
  have hqw := hmc.rg.w
  simp only [win, outside_cons, outside_nil, and_true] at hqw huw
  have eU : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → X.mem.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => hF1.readLE x n (by simp only [is1, outside_cons, outside_nil, and_true]; omega)
  have huacc : X.mem.accessible (c.uuP j) (8 * n') false = true := by
    rw [hmc.ev.fr.accessible]
    exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hua
      (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega))
  have t0 : (BitVec.ofNat 64 qv).toNat = qv := by rw [BitVec.toNat_ofNat]; omega
  have t3 : (BitVec.ofNat 64 (c.P s j U).length).toNat = (c.P s j U).length := by rw [BitVec.toNat_ofNat]; omega
  have t7 : (BitVec.ofNat 64 (c.uuP j)).toNat = c.uuP j := by
    rw [BitVec.toNat_ofNat]; simp only [Cx.uuP]; omega
  have t6 : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; simp only [Cx.uuL] at hle; omega
  have haccX : X.mem.accessible ((s.regs 4).toNat - 408) 48 true = true := by
    rw [hF1.accessible, hmc0.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hpre' : CmpSum.Pre X := by
    unfold CmpSum.Pre CmpSum.SliceOK
    rw [h0, h3, h7, h6, t0, t3, t7, t6, hspn, hra]
    refine ⟨by decide, by omega, by omega, by rw [show (s.regs 4).toNat - 400 - 8 = (s.regs 4).toNat - 408 by omega]; exact haccX, ?_, ?_⟩
    · by_cases hz : (c.P s j U).length = 0
      · exact Or.inl hz
      · refine Or.inr ⟨Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hqa
          (Nat.le_refl _) (by omega)), ?_⟩
        unfold Apart; omega
    · by_cases hz : n' = 0
      · exact Or.inl hz
      · refine Or.inr ⟨huacc, ?_⟩
        unfold Apart; simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega
  refine ReachesRet.call_regions (csumD impl hap) hpc hpre' fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v6, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  have hfw : MemFrame X.mem m (win X 8 40) := hf.mono fun x n ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hMF : MemFrame X.mem m (R.rt ++ win X 8 40 ++ [(0, 0)]) := hfw.mono fun x n ho => by
    simp only [outside_append] at ho; exact ho.1.2
  have hLF : LiveFrame X.mem m Lk [(0, 0)] := lf_winC _ hfw hLs
  have hinv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk m) :=
    inv_win hfw hout (by omega) hmc.ev.inv
  have hreg' : m.regions = X.mem.regions := hrg
  have rw' : ∀ x n, (x + n ≤ (s.regs 4).toNat - 408 ∨ (s.regs 4).toNat - 360 ≤ x) → m.readLE x n = X.mem.readLE x n :=
    fun x n h => hfw.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have kQ : m.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := rw' _ _ (by omega)
  have o0 : ∀ x n, Outside x n [(0, 0)] := fun x n => by simp only [outside_cons, outside_nil, and_true]; omega
  have a0 : ∀ x n, Apart x n 0 0 := fun x n => by unfold Apart; omega
  have ht0w := hcr.t0w
  simp only [win, outside_cons, outside_nil, and_true] at ht0w
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have hmcT : Mc R c s Lk bk m j Z U qv (stF c s j U) :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF (LiveExt.refl R Lk) hinv hreg' (Nat.le_refl _)
      (fun x n _ => o0 x n) (fun x n _ _ => o0 x n) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (a0 _ _) (a0 _ _) (a0 _ _) (a0 _ _) (a0 _ _)
      (by rw [limbs_congr (rw' _ _ (by omega))]; exact hmc.qk)
      (by rw [limbs_congr kQ]; exact hmc.bf)
      (by rw [limbs_congr (rw' _ _ (by omega))]; exact hmc.wk)
  -- the result
  have hlq : Asm.limbs X.mem qv (c.P s j U).length = (stF c s j U).buf.take (c.P s j U).length := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hPl]
  have hvX : natVal X.mem (c.uuP j) n' = natVal X.mem (c.uuP j) (c.uuL j) := by
    simp only [natVal]
    rw [eU (c.uuP j) (8 * n') (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega),
      eU (c.uuP j) (8 * c.uuL j) (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL]; omega)]
    exact hv
  have hNX : NatNorm X.mem (c.uuP j) n' := by
    rcases hN with h | h
    · exact Or.inl h
    · right; rw [eU _ _ (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega)]; exact h
  have hlu : Asm.limbs X.mem (c.uuP j) n' = Mdl.norm (stF c s j U).w := Asm.limbs_norm hmc.wk hvX hNX
  have hres : CmpSum.cmpRes (c.P s j U).length n' (Asm.lv X.mem qv (c.P s j U).length)
      (Asm.lv X.mem (c.uuP j) n') = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length (stF c s j U)) := by
    refine (Asm.cmp_model X.mem qv (c.uuP j) (c.P s j U).length n' _ rfl).trans ?_
    rw [hlq, hlu]; rfl
  refine k _ ?_ ?_ ?_ ?_ hfs hdf hx15 ?_ hmcT ⟨?_, ?_, ?_⟩
  · show retAddrOf X = _; simp only [retAddrOf]; rw [hspn, hra]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [hsp]; bv_omega
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · simp only [setRegF_apply, ↓reduceIte]
    rw [h3, h6, h0, h7, t0, t3, t7, t6]; exact hres
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s328
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s152
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s168

end FvModexp.Amd64.Q.DivRec
