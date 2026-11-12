import FvModexp.Proofs.Arm64.Nat.DrsD5R
import FvModexp.Proofs.Arm64.Nat.DrsDG
import FvModexp.Proofs.Arm64.Nat.DrsC3

/-!
# `divRecursiveStep` (arm64), after the correction loop: `subVW(uu[ql:], uu[ql:], c)` (natdiv.go:849)

`d5`: from `d5r`'s `CALL subVW` state (borrow `c = 1`, `Mc` at `stS ql stF`) → `subVW` (`vwSum`) → its return
`0x1ba8d4` with `Mc` at `Cx.stG` (`uu` = `(subToC …).1`); `stS_zero`: with borrow `0` the state `stS ql stF` already
is `Cx.stG`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

theorem upd_app_full (A D X : List Nat) (h : X.length = D.length) : Mdl.upd (A ++ D) A.length X = A ++ X := by
  unfold Mdl.upd
  rw [List.take_left, List.drop_eq_nil_of_le (by simp; omega)]; simp

theorem stS_zero {c : Cx} {s : State} {j : Nat} {U : List Nat} (hbl : (c.stF s j U).buf.length = 3 * c.vl)
    (hq : (c.P s j U).length ≤ 3 * c.vl)
    (h0 : (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length) ((c.stF s j U).buf.take (c.P s j U).length)).2 = 0) :
    stS (c.P s j U).length (c.stF s j U) = c.stG s j U := by
  have hx : ((c.stF s j U).buf.take (c.P s j U).length).length = (c.P s j U).length := by
    rw [List.length_take, hbl]; omega
  simp only [stS, Cx.stG, Cx.sT, Mdl.subToC, hx, h0]
  rfl

theorem sT_one {c : Cx} {s : State} {j : Nat} {U : List Nat} (hbl : (c.stF s j U).buf.length = 3 * c.vl)
    (hq : (c.P s j U).length ≤ 3 * c.vl)
    (h1 : (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length) ((c.stF s j U).buf.take (c.P s j U).length)).2 = 1) :
    (c.sT s j U).1 = (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length)
        ((c.stF s j U).buf.take (c.P s j U).length)).1 ++
      (Mdl.subVW ((c.stF s j U).w.drop (c.P s j U).length) 1).1 := by
  have hx : ((c.stF s j U).buf.take (c.P s j U).length).length = (c.P s j U).length := by
    rw [List.length_take, hbl]; omega
  simp only [Cx.sT, Mdl.subToC, hx, h1]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(uu[ql:], uu[ql:], 1)`** from its call state -/
theorem d5 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (Q : State → Prop)
    (Y : State) (hpc : Y.pc = BitVec.ofNat 64 SubVW.entry) (h30 : Y.regs 30 = BitVec.ofNat 64 rD5)
    (hsp : Y.sp = s.sp - 400#64) (h28 : Y.regs 28 = s.regs 28) (h29 : Y.regs 29 = s.sp - 408#64)
    (h18 : Y.regs 18 = s.regs 18)
    (h0 : Y.regs 0 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length))
    (h1 : Y.regs 1 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length))
    (h2 : Y.regs 2 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length))
    (h3 : Y.regs 3 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length))
    (h4 : Y.regs 4 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length))
    (h5 : Y.regs 5 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length)) (h6 : Y.regs 6 = 1#64)
    (M0 : Memory) (hwE : Asm.limbs M0 (c.uuP j) (c.uuL j) = (c.stF s j U).w)
    (hmc : Mc R c s Lk bk Y.mem j Z U qv (stS (c.P s j U).length (c.stF s j U)))
    (hv4 : V4 c s Y.mem qv (c.P s j U).length)
    (hb1 : (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length)
      ((c.stF s j U).buf.take (c.P s j U).length)).2 = 1)
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rD5 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      Mc R c s L' b' T.mem j Z U qv (c.stG s j U) → V4 c s T.mem qv (c.P s j U).length →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, huh, huw, hug⟩,
    ⟨-, -, -, -, -, -, -⟩, hqu, -, huv, -, ⟨-, -, -, -, hup8, -⟩, -, ⟨hus, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hspn : Y.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk Y 4144 40 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨g1, g2, -, g4, g5, g6, g7, -⟩ := hce'
  have hPl := P_len_le2 (c := c) (s := s) (j := j) (U := U) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hXacc : ∀ a n v, Y.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hmc.ev.fr.accessible]
  simp only [win, outside_cons, outside_nil, and_true] at huw
  -- the slice `uu[ql:]`
  have ep : c.uuP j + 8 * (c.P s j U).length = c.up + 8 * (j - c.vl / 2 + (c.P s j U).length) := by
    simp only [Cx.uuP]; omega
  have t0 := tN (by simp only [Cx.uuP]; omega : c.uuP j + 8 * (c.P s j U).length < 2 ^ 64)
  have t1 := tN (by simp only [Cx.uuL]; omega : c.uuL j - (c.P s j U).length < 2 ^ 64)
  have t2 := tN (by simp only [Cx.uuC]; omega : c.uuC j - (c.P s j U).length < 2 ^ 64)
  have t6 : (1#64 : BitVec 64).toNat = 1 := rfl
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 1) (Y.regs 2) (Y.regs 3)
    (Y.regs 4) (Y.regs 5) (Y.regs 6)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?xz, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 rD5 : BitVec 64).toNat = rD5 := by decide
    rw [h30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case xz => rw [h4, h1]
  case pre =>
    have e03 : Y.regs 0 = Y.regs 3 := by rw [h0, h3]
    unfold SubVW.Pre
    rw [if_pos e03]
    rw [h0, h1, h2, h3, h5, t0, t1, t2, ep]
    simp only [Cx.uuL, Cx.uuC] at hulc ⊢
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
      Outside x n [(c.uuP j + 8 * (c.P s j U).length,
        c.uuP j + 8 * (c.P s j U).length + 8 * (c.uuL j - (c.P s j U).length))] →
      T.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have t0u := hcr.t0u
  have kT : T.mem.readLE c.t0 (8 * (c.q0 s j U).length) = Y.mem.readLE c.t0 (8 * (c.q0 s j U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true]; omega
  have kQ : T.mem.readLE qv (8 * (3 * c.vl)) = Y.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h (by have := hrg.w; exact this) ?_
    have := hrg.u; unfold Apart at this; simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true]; omega
  -- `uu` after the call
  have hql3 : (c.P s j U).length ≤ 3 * c.vl := by omega
  have hqlu : (c.P s j U).length ≤ c.uuL j := by simp only [Cx.uuL]; omega
  have hbf := hmc.bf
  have hbl : (c.stF s j U).buf.length = 3 * c.vl := by
    simp only [stS] at hbf; rw [← hbf, Asm.length_limbs]
  have hbW : Mdl.Wd (c.stF s j U).buf := by simp only [stS] at hbf; rw [← hbf]; exact Asm.Wd_limbs _ _ _
  have hwW : Mdl.Wd (c.stF s j U).w := by rw [← hwE]; exact Asm.Wd_limbs _ _ _
  have hwl : (c.stF s j U).w.length = c.uuL j := by rw [← hwE, Asm.length_limbs]
  have hr1 := (Mdl.subVVc_spec ((c.stF s j U).w.take (c.P s j U).length) ((c.stF s j U).buf.take (c.P s j U).length) 0
    (hwW.take _) (hbW.take _) (by rw [List.length_take, List.length_take, hwl, hbl]; omega) (by omega)).1
  rw [List.length_take, hwl, Nat.min_eq_left hqlu] at hr1
  have hDW : Mdl.Wd ((c.stF s j U).w.drop (c.P s j U).length) := hwW.drop _
  have hY : Asm.limbs Y.mem (c.uuP j + 8 * (c.P s j U).length) (c.uuL j - (c.P s j U).length) =
      (c.stF s j U).w.drop (c.P s j U).length := by
    rw [← Asm.limbs_drop, hmc.wk]
    simp only [stS]
    exact List.drop_left' hr1
  have hz := (Asm.subVW_model Y.mem T.mem _ _ _ 1 _ (by omega) hval hr0).1
  rw [hY] at hz
  have hX := (Mdl.subVW_spec ((c.stF s j U).w.drop (c.P s j U).length) 1 hDW (by omega)).1
  have hwk : Asm.limbs T.mem (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) = (c.stG s j U).w := by
    rw [Asm.limbs_upd (m := Y.mem) (j := (c.P s j U).length) (k := c.uuL j - (c.P s j U).length)
      (by simp only [Cx.uuL] at hqlu ⊢; omega)
      (fun i hi hi2 => rk (c.up + 8 * (j - c.vl / 2) + 8 * i) 8
        (hext.held (huh.sub (by simp only [Cx.uuL] at hqlu; omega) (by simp only [Cx.uuL] at hqlu; omega)))
        (by simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu hi2 ⊢; omega)), hmc.wk]
    show Mdl.upd _ _ (Asm.limbs T.mem (c.uuP j + 8 * (c.P s j U).length) (c.uuL j - (c.P s j U).length)) = _
    rw [hz]
    simp only [Cx.stG, stS]
    rw [sT_one hbl hql3 hb1]
    have hr1' : (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length)
        ((c.stF s j U).buf.take (c.P s j U).length)).1.length = (c.P s j U).length := hr1
    have e := upd_app_full (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length)
        ((c.stF s j U).buf.take (c.P s j U).length)).1 ((c.stF s j U).w.drop (c.P s j U).length)
      (Mdl.subVW ((c.stF s j U).w.drop (c.P s j U).length) 1).1 hX
    rw [hr1'] at e
    exact e
  have hloc := hmc.qloc.out
  have hmcT : Mc R c s L' b' T.mem j Z U qv (c.stG s j U) :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun x n h => by
        simp only [Cx.ws, stkWs, Cx.uuP, Cx.uuL, outside_append, outside_cons, outside_nil, and_true] at h hqlu ⊢; omega)
      (fun x n _ h => by
        simp only [Cx.ws, stkWs, Cx.uuP, Cx.uuL, outside_append, outside_cons, outside_nil, and_true] at h hqlu ⊢; omega)
      (by simp only [win, Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega)
      (by unfold Apart at hus ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart at huv ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart at hqu ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart; simp only [Cx.uuP]; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ winA Y 4144 40 ++ [(c.uuP j + 8 * (c.P s j U).length,
        c.uuP j + 8 * (c.P s j U).length + 8 * (c.uuL j - (c.P s j U).length))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega) (by omega) (by omega))
  exact k T (by rw [hT, h30]) (f1.trans hsp) (f2.trans h28) (f3.trans h29) (f4.trans h18) L' b' hmcT
    (hv4.frame hMF hhi h0')

end FvModexp.Arm64.DivRec
