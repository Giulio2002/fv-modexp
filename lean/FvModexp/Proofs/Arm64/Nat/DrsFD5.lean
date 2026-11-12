import FvModexp.Proofs.Arm64.Nat.DrsFD5R
import FvModexp.Proofs.Arm64.Nat.DrsD5
import FvModexp.Proofs.Arm64.Nat.DrsDG
import FvModexp.Proofs.Arm64.Nat.DrsC3

/-!
# `divRecursiveStep` (arm64), final block: `c = subVW(u[ql:], u[ql:], c)`; `if c != 0 { panic }` (natdiv.go:886-888)

`Cx.sGF` (the model after `u -= qhatv`), `stSF_zero`, `sTF_one`; `d5F`: the call (`vwSum`) → `McF` at `sGF`; its
carry is `0` (`hc0`, from `c_zeroF`), so the `CBNZ` falls through to `0x1bac98`. Adapted from DrsD5.
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the model state after `u -= qhatv` (with the borrow) at the end of the final block -/
@[reducible] def Cx.sGF (c : Cx) (s : State) (U : List Nat) : Mdl.St := { c.sFF s U with w := (c.sTF s U).1 }

theorem stSF_zero {c : Cx} {s : State} {U : List Nat} (hbl : (c.sFF s U).buf.length = 3 * c.vl)
    (hq : (c.PF s U).length ≤ 3 * c.vl)
    (h0 : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length) ((c.sFF s U).buf.take (c.PF s U).length)).2 = 0) :
    stS (c.PF s U).length (c.sFF s U) = c.sGF s U := by
  have hx : ((c.sFF s U).buf.take (c.PF s U).length).length = (c.PF s U).length := by
    rw [List.length_take, hbl]; omega
  simp only [stS, Cx.sGF, Cx.sTF, Mdl.subToC, hx, h0]
  rfl

theorem sTF_one {c : Cx} {s : State} {U : List Nat} (hbl : (c.sFF s U).buf.length = 3 * c.vl)
    (hq : (c.PF s U).length ≤ 3 * c.vl)
    (h1 : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length) ((c.sFF s U).buf.take (c.PF s U).length)).2 = 1) :
    c.sTF s U = ((Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
        ((c.sFF s U).buf.take (c.PF s U).length)).1 ++
      (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).1,
      (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).2) := by
  have hx : ((c.sFF s U).buf.take (c.PF s U).length).length = (c.PF s U).length := by
    rw [List.length_take, hbl]; omega
  simp only [Cx.sTF, Mdl.subToC, hx, h1]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(uu[ql:], uu[ql:], 1)`** from its call state -/
theorem d5F (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (Q : State → Prop)
    (Y : State) (hpc : Y.pc = BitVec.ofNat 64 SubVW.entry) (h30 : Y.regs 30 = BitVec.ofNat 64 rFD5W)
    (hsp : Y.sp = s.sp - 400#64) (h28 : Y.regs 28 = s.regs 28) (h29 : Y.regs 29 = s.sp - 408#64)
    (h18 : Y.regs 18 = s.regs 18)
    (h0 : Y.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length))
    (h1 : Y.regs 1 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length))
    (h2 : Y.regs 2 = BitVec.ofNat 64 (c.uc - (c.PF s U).length))
    (h3 : Y.regs 3 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length))
    (h4 : Y.regs 4 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length))
    (h5 : Y.regs 5 = BitVec.ofNat 64 (c.uc - (c.PF s U).length)) (h6 : Y.regs 6 = 1#64)
    (M0 : Memory) (hwE : Asm.limbs M0 c.up c.u1 = (c.sFF s U).w)
    (hmc : McF R c s Lk bk Y.mem j Z U qv (stS (c.PF s U).length (c.sFF s U)))
    (hv4 : V3F c s Y.mem qv (c.PF s U).length)
    (hb1 : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
      ((c.sFF s U).buf.take (c.PF s U).length)).2 = 1)
    (hc0 : (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).2 = 0)
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rFD5 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      McF R c s L' b' T.mem j Z U qv (c.sGF s U) → V3F c s T.mem qv (c.PF s U).length →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, huh, huw, hug⟩,
    ⟨-, -, -, -, -, -, -⟩, hqu, -, huv, -, ⟨-, -, -, -, hup8, -⟩, -, ⟨hus, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hvu := hcr.vu1
  have hjB := hmc.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hspn : Y.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk Y 4144 40 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨g1, g2, -, g4, g5, g6, g7, -⟩ := hce'
  have hPl := PF_len_le2 (c := c) (s := s) (U := U) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hXacc : ∀ a n v, Y.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hmc.ev.fr.accessible]
  simp only [win, outside_cons, outside_nil, and_true] at huw
  -- the slice `uu[ql:]`
  have t0 := tN (by omega : c.up + 8 * (c.PF s U).length < 2 ^ 64)
  have t1 := tN (by omega : c.u1 - (c.PF s U).length < 2 ^ 64)
  have t2 := tN (by omega : c.uc - (c.PF s U).length < 2 ^ 64)
  have t6 : (1#64 : BitVec 64).toNat = 1 := rfl
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 1) (Y.regs 2) (Y.regs 3)
    (Y.regs 4) (Y.regs 5) (Y.regs 6)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?xz, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 rFD5W : BitVec 64).toNat = rFD5W := by decide
    rw [h30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case xz => rw [h4, h1]
  case pre =>
    have e03 : Y.regs 0 = Y.regs 3 := by rw [h0, h3]
    unfold SubVW.Pre
    rw [if_pos e03]
    rw [h0, h1, h2, h3, h5, t0, t1, t2]
    refine ⟨⟨g1, g2, g4, g5, g6, g7⟩, by omega, by omega, by omega, by omega, fun _ => ⟨by omega,
      hext.held (huh.sub (by omega) (by omega)), by rw [hXacc]; exact Memory.accessible_mono _ hua (by omega) (by omega),
      by omega⟩, ?_, ?_, ?_, by omega, hext.held (huh.sub (by omega) (by omega)), ?_, by first | exact Or.inl rfl | exact Or.inl trivial,
      by rw [h28]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h28]; unfold Apart at hug ⊢; omega
    · rw [hXacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hua (by omega) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h1, h3, h6, t0, t1, t6] at hq
  obtain ⟨hr0, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T.mem.regions = Y.mem.regions := hrgT
  rw [h28] at hinv
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.up + 8 * (c.PF s U).length,
        c.up + 8 * (c.PF s U).length + 8 * (c.u1 - (c.PF s U).length))] →
      T.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have t0u := hcr.t0u
  have kT : T.mem.readLE c.t0 (8 * (c.qF s U).length) = Y.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : T.mem.readLE qv (8 * (3 * c.vl)) = Y.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h (by have := hrg.w; exact this) ?_
    have := hrg.u; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  -- `uu` after the call
  have hql3 : (c.PF s U).length ≤ 3 * c.vl := by omega
  have hqlu : (c.PF s U).length ≤ c.u1 := by omega
  have hbf := hmc.bf
  have hbl : (c.sFF s U).buf.length = 3 * c.vl := by
    simp only at hbf; rw [← hbf, Asm.length_limbs]
  have hbW : Mdl.Wd (c.sFF s U).buf := by simp only at hbf; rw [← hbf]; exact Asm.Wd_limbs _ _ _
  have hwW : Mdl.Wd (c.sFF s U).w := by rw [← hwE]; exact Asm.Wd_limbs _ _ _
  have hwl : (c.sFF s U).w.length = c.u1 := by rw [← hwE, Asm.length_limbs]
  have hr1 := (Mdl.subVVc_spec ((c.sFF s U).w.take (c.PF s U).length) ((c.sFF s U).buf.take (c.PF s U).length) 0
    (hwW.take _) (hbW.take _) (by rw [List.length_take, List.length_take, hwl, hbl]; omega) (by omega)).1
  rw [List.length_take, hwl, Nat.min_eq_left hqlu] at hr1
  have hDW : Mdl.Wd ((c.sFF s U).w.drop (c.PF s U).length) := hwW.drop _
  have hY : Asm.limbs Y.mem (c.up + 8 * (c.PF s U).length) (c.u1 - (c.PF s U).length) =
      (c.sFF s U).w.drop (c.PF s U).length := by
    rw [← Asm.limbs_drop, hmc.wk]
    simp only [stS]
    exact List.drop_left' hr1
  have hz := (Asm.subVW_model Y.mem T.mem _ _ _ 1 _ (by omega) hval hr0).1
  rw [hY] at hz
  have hX := (Mdl.subVW_spec ((c.sFF s U).w.drop (c.PF s U).length) 1 hDW (by omega)).1
  have hwk : Asm.limbs T.mem c.up c.u1 = (c.sGF s U).w := by
    rw [Asm.limbs_upd (m := Y.mem) (j := (c.PF s U).length) (k := c.u1 - (c.PF s U).length)
      (by omega)
      (fun i hi hi2 => rk (c.up + 8 * i) 8
        (hext.held (huh.sub (by omega) (by omega)))
        (by simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true] at hi2 ⊢; omega)), hmc.wk]
    show Mdl.upd _ _ (Asm.limbs T.mem (c.up + 8 * (c.PF s U).length) (c.u1 - (c.PF s U).length)) = _
    rw [hz]
    simp only [stS]
    rw [sTF_one hbl hql3 hb1]
    have hr1' : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
        ((c.sFF s U).buf.take (c.PF s U).length)).1.length = (c.PF s U).length := hr1
    have e := upd_app_full (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
        ((c.sFF s U).buf.take (c.PF s U).length)).1 ((c.sFF s U).w.drop (c.PF s U).length)
      (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).1 hX
    rw [hr1'] at e
    exact e
  have hloc := hmc.qloc.out
  have hmcT : McF R c s L' b' T.mem j Z U qv (c.sGF s U) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun x n h => by
        simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega)
      (fun x n _ h => by
        simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hus ⊢; omega)
      (by unfold Apart at huv ⊢; omega)
      (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ winA Y 4144 40 ++ [(c.up + 8 * (c.PF s U).length,
        c.up + 8 * (c.PF s U).length + 8 * (c.u1 - (c.PF s U).length))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  have hv3T := hv4.frame hMF hhi h0'
  have hr := (Asm.subVW_model Y.mem T.mem _ _ _ 1 _ (by omega) hval hr0).2
  rw [hY, hc0] at hr
  have h0T : T.regs 0 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hr]; rfl)
  have hpcT : T.pc = BitVec.ofNat 64 rFD5W := by rw [hT, h30]
  have hspT : T.sp = s.sp - 400#64 := f1.trans hsp
  have h28T : T.regs 28 = s.regs 28 := f2.trans h28
  have h29T : T.regs 29 = s.sp - 408#64 := f3.trans h29
  have h18T : T.regs 18 = s.regs 18 := f4.trans h18
  have hB1 : Box (McF R c s L' b' T.mem j Z U qv (c.sGF s U)) := ⟨hmcT⟩
  have hB2 : Box (V3F c s T.mem qv (c.PF s U).length) := ⟨hv3T⟩
  clear hmcT hv3T hmc hv4 hMF hLF hval hr0 hz hY hr kT kQ hwk rk hT h30 hpc
  janus_run [h0T] until [rFD5]
  refine k _ rfl rfl ?_ ?_ ?_ L' b' hB1.1 hB2.1
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28T
  · exact h29T
  · exact h18T

end FvModexp.Arm64.DivRec
