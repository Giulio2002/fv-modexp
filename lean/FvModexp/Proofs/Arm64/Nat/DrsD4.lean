import FvModexp.Proofs.Arm64.Nat.DrsSegD
import FvModexp.Proofs.Arm64.Nat.DrsWs
/-!
# `divRecursiveStep` (arm64), after the correction loop: `c := subVV(uu[:ql], uu[:ql], qhatv)` (natdiv.go:847)
`d4`: from `d3`'s call state → `subVV.abi0` (`svvD`) → its return `0x1ba884` with `Mc` at `stS ql st` (`uu[:ql] -= qhatv`)
and the borrow at `SP'+80`.
-/
set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`c := subVV(uu[:ql], uu[:ql], qhatv)`** from its call state -/
theorem d4 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (st : Mdl.St) (Q : State → Prop) (T : State) (hmc0 : Mc R c s Lk bk T.mem j Z U qv st)
    (hv4 : V4 c s T.mem qv (c.P s j U).length)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 subVVA) (h30 : X.regs 30 = BitVec.ofNat 64 0x1ba884)
    (hsp : X.sp = s.sp - 400#64) (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64)
    (h18 : X.regs 18 = s.regs 18) (hF : MemFrame T.mem X.mem (isA s)) (hreg : X.mem.regions = T.mem.regions)
    (ez : X.mem.readLE (s.sp.toNat - 392) 8 = c.uuP j) (en : X.mem.readLE (s.sp.toNat - 384) 8 = (c.P s j U).length)
    (ex : X.mem.readLE (s.sp.toNat - 368) 8 = c.uuP j) (ey : X.mem.readLE (s.sp.toNat - 344) 8 = qv)
    (k : ∀ T' : State, T'.pc = BitVec.ofNat 64 0x1ba884 → T'.sp = s.sp - 400#64 → T'.regs 28 = s.regs 28 →
      T'.regs 29 = s.sp - 408#64 → T'.regs 18 = s.regs 18 →
      Mc R c s Lk bk T'.mem j Z U qv (stS (c.P s j U).length st) → V4 c s T'.mem qv (c.P s j U).length →
      T'.mem.readLE (s.sp.toNat - 320) 8 =
        (Mdl.subVV (st.w.take (c.P s j U).length) (st.buf.take (c.P s j U).length)).2 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hmc0.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, huh, huw, hug⟩,
    ⟨-, hv48, -, -, -, -, -⟩, hqu, -, huv, -, -, -, ⟨hus, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, hga, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hmc := Mc.ownA hmc0 hF hreg
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 0 88 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨-, -, -, -, -, -, hLs, -⟩ := hce'
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hrw := hrg.w
  simp only [win, outside_cons, outside_nil, and_true] at hrw huw
  have hPl := P_len_le2 (c := c) (s := s) (j := j) (U := U) (by omega)
  have hql3 : (c.P s j U).length ≤ 3 * c.vl := by omega
  have hqlu : (c.P s j U).length ≤ c.uuL j := Nat.le_trans hPl (uuL_ge hjm hcr.vu1)
  -- the frame words, at `X.sp`
  have e8 : X.sp.toNat + 8 = s.sp.toNat - 392 := by omega
  have e16 : X.sp.toNat + 16 = s.sp.toNat - 384 := by omega
  have e32 : X.sp.toNat + 32 = s.sp.toNat - 368 := by omega
  have e56 : X.sp.toNat + 56 = s.sp.toNat - 344 := by omega
  have e80 : X.sp.toNat + 80 = s.sp.toNat - 320 := by omega
  have ez' : X.mem.readLE (X.sp.toNat + 8) 8 = c.uuP j := by rw [e8]; exact ez
  have en' : X.mem.readLE (X.sp.toNat + 16) 8 = (c.P s j U).length := by rw [e16]; exact en
  have ex' : X.mem.readLE (X.sp.toNat + 32) 8 = c.uuP j := by rw [e32]; exact ex
  have ey' : X.mem.readLE (X.sp.toNat + 56) 8 = qv := by rw [e56]; exact ey
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF.accessible, hmc0.ev.fr.accessible]
  have hzacc : X.mem.accessible (c.uuP j) (8 * (c.P s j U).length) true = true := by
    rw [hXacc]; exact Memory.accessible_mono _ hua (by simp only [Cx.uuP]; omega)
      (by simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
  have hpre : VVLPre R bk Lk X := by
    unfold VVLPre
    rw [ez', en']
    refine ⟨?_, by rw [h28]; exact hmc.ev.inv, hext.held (huh.sub (by simp only [Cx.uuP]; omega)
      (by simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)), hout.of_sub (by omega) (by omega), ?_, ?_⟩
    · unfold VVPre
      rw [ez', en', ex', ey']
      refine ⟨ez', en', ex', ey', by rw [h30]; decide, by rw [h30]; decide, by rw [hspn]; omega, by omega,
        by rw [hXacc]; exact Memory.accessible_mono _ hw (by omega) (by omega), hzacc,
        Memory.accessible_weaken _ hzacc,
        Memory.accessible_weaken _ (Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega)), Or.inl rfl, Or.inr ?_, ?_⟩
      · have := hrg.u; unfold Apart at this ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega
      · rw [hspn]; unfold Apart; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega
    · rw [h28]; unfold Apart at hug ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega
    · rw [h28]; unfold Apart at hga ⊢; omega
  refine ReachesRet.call_regions (svvD impl hap R bk Lk) hpc hpre fun T' hT hq hrgT => ?_
  obtain ⟨junk, f, v, fpsr, m, rfl, ⟨hval, hcar, hfr⟩, hinv, -⟩ := hq
  simp only [ez', en', ex', ey', e80] at hval hcar hfr
  rw [h28] at hinv
  have hregm : m.regions = X.mem.regions := hrgT
  have hcar1 : m.readLE (s.sp.toNat - 320) 8 ≤ 1 := by rw [hcar]; split <;> omega
  obtain ⟨hz1, hb1⟩ := Asm.subVV_model X.mem m (c.uuP j) (c.uuP j) qv (c.P s j U).length _ hcar1 hval
  have hWt : Asm.limbs X.mem (c.uuP j) (c.P s j U).length = st.w.take (c.P s j U).length := by
    rw [← hmc.wk, Asm.limbs_take _ _ _ _ hqlu]
  have hBt : Asm.limbs X.mem qv (c.P s j U).length = st.buf.take (c.P s j U).length := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hql3]
  have hwk : Asm.limbs m (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) = (stS (c.P s j U).length st).w := by
    rw [Asm.limbs_upd (m := X.mem) (j := 0) (k := (c.P s j U).length) (by simp only [Cx.uuL] at hqlu; omega)
      (fun i hi hi2 => hfr.readLE _ _ (by simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega)),
      Mdl.upd_zero, hmc.wk]
    simp only [Nat.mul_zero, Nat.add_zero, Asm.length_limbs]
    rw [hz1, hWt, hBt]
  -- the frame of the call in the `Mc.callN` form
  have hF' : MemFrame X.mem m (R.rt ++ winA X 0 88 ++ [(c.uuP j, c.uuP j + 8 * (c.P s j U).length)]) :=
    hfr.mono fun x n ho => by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      rw [hspn] at ho; omega
  have hL' : LiveFrame X.mem m Lk [(c.uuP j, c.uuP j + 8 * (c.P s j U).length)] := ⟨fun x n hin ho => hfr.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ho ⊢
    rw [hspn] at this; omega)⟩
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.uuP j, c.uuP j + 8 * (c.P s j U).length)] → m.readLE x n = X.mem.readLE x n :=
    fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hF' hL' hh hw' ho
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have t0u := hcr.t0u
  have kT : m.readLE c.t0 (8 * (c.q0 s j U).length) = X.mem.readLE c.t0 (8 * (c.q0 s j U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega
  have kQ : m.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h (by simp only [win, outside_cons, outside_nil, and_true]; omega) ?_
    have := hrg.u; unfold Apart at this
    simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega
  have hmcT : Mc R c s Lk bk m j Z U qv (stS (c.P s j U).length st) :=
    Mc.callN hmc hspn (by omega) (by omega) hF' hL' (LiveExt.refl R Lk) hinv hregm (Nat.le_refl _)
      (fun _ _ h => ws_up h (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega))
      (fun _ _ _ h => ws_up0 h (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega))
      (by simp only [win, Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega)
      (by unfold Apart at hus ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart at huv ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart at hqu ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart; simp only [Cx.uuP]; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  -- the slots
  have o : ∀ a, (a + 8 ≤ s.sp.toNat - 320 ∨ s.sp.toNat - 312 ≤ a) → s.sp.toNat - 408 ≤ a →
      a + 8 ≤ s.sp.toNat + 96 → m.readLE a 8 = X.mem.readLE a 8 := fun a h1 h2 h3 => hfr.readLE _ _ (by
    simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega)
  refine k _ (by show X.regs 30 = _; exact h30) hsp (by rw [ret0_r _ _ _ _ _ _ 28 (by omega)]; exact h28)
    (by rw [ret0_r _ _ _ _ _ _ 29 (by omega)]; exact h29) (by rw [ret0_r _ _ _ _ _ _ 18 (by omega)]; exact h18) hmcT
    ⟨?_, ?_, ?_⟩ ?_
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hv4.s328
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hv4.s152
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hv4.s168
  · show m.readLE _ _ = _
    rw [← hWt, ← hBt]; exact hb1

end FvModexp.Arm64.DivRec
