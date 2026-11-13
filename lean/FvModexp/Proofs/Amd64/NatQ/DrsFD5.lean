import FvModexp.Proofs.Amd64.NatQ.DrsFD5R
import FvModexp.Proofs.Amd64.NatQ.DrsDG
import FvModexp.Proofs.Amd64.NatQ.DrsC5
import FvModexp.Proofs.Amd64.NatQ.DrsC6
import FvModexp.Proofs.Amd64.NatQ.DrsD5
import FvModexp.Proofs.Amd64.NatQ.DrsFV
import FvModexp.Proofs.Amd64.NatQ.DrsFD4

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFD5.lean; adapted from Amd64/NatQ/DrsD5.lean)
# `divRecursiveStep` (amd64), final block: `c = subVW(u[ql:], u[ql:], c)`; `if c != 0 { panic }` (natdiv.go:884-887)

`Cx.sGF` (the model after `u -= qhatv`), `stSF_zero`, `sTF_one`; `d5F`: from the `CALL subVW` entry `Y` (`RSP = r - 400`,
return `0x5f0628`) → `subVW` (`SubVW.ens` on `LibDrs`, in place on `u[ql:]`, `y = 1`) → its return with `RAX` = the
borrow `= 0` (`hc0`, from `c_zeroF`) → `MOVQ AX, R9; TESTQ R9, R9; JA` (gopanic) not taken → `0x5f0630` (`rJF6`)
with `McF … sGF`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

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
/-- the return site `0x5f0628` is admissible for `subVW`'s program -/
theorem raFD5W (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments [SubVW.fn]).link impl) rFD5W := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := [SubVW.fn])
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0xda8 (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(uu[ql:], uu[ql:], 1)`** from its callee entry -/
theorem d5F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (Q : State → Prop) (T : State)
    (hmc0 : McF R c s Lk bk T.mem j Z U qv (stS (c.PF s U).length (c.sFF s U)))
    (hv40 : V3F c s T.mem qv (c.PF s U).length)
    (Y : State) (hpc : Y.rip = BitVec.ofNat 64 SubVW.entry) (hsp : Y.regs 4 = s.regs 4 - 400#64)
    (h5 : Y.regs 5 = s.regs 4 - 8#64) (h14 : Y.regs 14 = s.regs 14) (hfs : Y.fsBase = s.fsBase)
    (hdf : Y.df = false) (hx15 : Y.xmm 15 = 0#128)
    (h0 : Y.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length))
    (h3 : Y.regs 3 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length))
    (h1 : Y.regs 1 = BitVec.ofNat 64 (c.uc - (c.PF s U).length))
    (h7 : Y.regs 7 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length))
    (h6 : Y.regs 6 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length))
    (h8 : Y.regs 8 = BitVec.ofNat 64 (c.uc - (c.PF s U).length)) (h9 : Y.regs 9 = 1#64)
    (hFR : MemFrame T.mem Y.mem (isR s)) (hreg0 : Y.mem.regions = T.mem.regions)
    (hra : Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rFD5W)
    (M0 : Memory) (hwE : Asm.limbs M0 c.up c.u1 = (c.sFF s U).w)
    (hb1 : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
      ((c.sFF s U).buf.take (c.PF s U).length)).2 = 1)
    (hc0 : (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).2 = 0)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rJF6 → T'.regs 4 = s.regs 4 - 392#64 → T'.regs 5 = s.regs 4 - 8#64 →
      T'.regs 14 = s.regs 14 → T'.fsBase = s.fsBase → T'.df = false → T'.xmm 15 = 0#128 →
      ∀ (L' : List (Nat × Nat)) (b' : Nat),
      McF R c s L' b' T'.mem j Z U qv (c.sGF s U) → V3F c s T'.mem qv (c.PF s U).length →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q := by
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hua, hu48, huh, huw, hug⟩ := hpre.ua
  have hulc := hpre.ulc; have huc40 := hpre.uc40; have hv9 := hpre.v9.1
  have hqu := hpre.qu; have huv := hpre.uv; have hus := hpre.su.1; have hutl := hpre.tl.2.1
  have hup8 : c.up % 8 = 0 := hpre.stl.2.2.2.2.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40; have hvu := hcr.vu1
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame T.mem Y.mem (is1F s) := hFR.mono fun x n ho => by
    simp only [isR, is1F, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := McF.own1 hmc0 hF1 hreg0
  have hv4 := V3F.own1 hv40 hF1 h0'
  have hspn : (Y.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : Callees.CallEnvND R Lk Y 4136 40 := by
    obtain ⟨g1, g2, g3, -, g5, g6, g7, g8, -, g10, g11, g12⟩ :=
      Ev.callEnv (k := 4136) (a := 40) hcr hmc.ev hspn h14 hfs (by omega) (by omega)
    exact ⟨g1, g2, g3, g5, g6, g7, g8, g10, g11, g12⟩
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
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 3) (Y.regs 1) (Y.regs 7)
    (Y.regs 6) (Y.regs 8) (Y.regs 9)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?xz, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra => rw [show (Y.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raFD5W impl hap
  case xz => rw [h6, h3]
  case pre =>
    have e07 : Y.regs 0 = Y.regs 7 := by rw [h0, h7]
    unfold SubVW.Pre
    rw [if_pos e07]
    rw [h0, h3, h1, h7, h8, t0, t1, t2]
    refine ⟨hce', by omega, by omega, by omega, by omega, fun _ => ⟨by omega,
      hext.held (huh.sub (by omega) (by omega)), by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega),
      by omega⟩, ?_, ?_, ?_, by omega, hext.held (huh.sub (by omega) (by omega)), ?_, Or.inl rfl,
      by rw [h14]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h14, hfs]; unfold Apart at hug hutl ⊢; (try simp only [grd, tls]); omega
    · rw [hXacc]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h3, h7, h9, t0, t1, t6] at hq
  obtain ⟨g1, g2, hcr0, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = Y.mem.regions := hrgT
  rw [h14] at hinv
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.up + 8 * (c.PF s U).length,
        c.up + 8 * (c.PF s U).length + 8 * (c.u1 - (c.PF s U).length))] →
      T'.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have t0u := hcr.t0u
  have kT : T'.mem.readLE c.t0 (8 * (c.qF s U).length) = Y.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : T'.mem.readLE qv (8 * (3 * c.vl)) = Y.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h (by have := hrg.w; exact this) ?_
    have := hrg.u; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  -- `uu` after the call
  have hql3 : (c.PF s U).length ≤ 3 * c.vl := by omega
  have hqlu : (c.PF s U).length ≤ c.u1 := Nat.le_trans hPl (by have := hcr.vu1; omega)
  have hbf := hmc.bf
  have hbl : (c.sFF s U).buf.length = 3 * c.vl := by
    simp only [stS] at hbf; rw [← hbf, Asm.length_limbs]
  have hbW : Mdl.Wd (c.sFF s U).buf := by simp only [stS] at hbf; rw [← hbf]; exact Asm.Wd_limbs _ _ _
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
  have hzc := Asm.subVW_model Y.mem T'.mem _ _ _ 1 (T'.regs 0).toNat (by omega) hval hcr0
  rw [hY] at hzc
  have hz := hzc.1
  have hax : T'.regs 0 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hzc.2, hc0]; rfl)
  have hX := (Mdl.subVW_spec ((c.sFF s U).w.drop (c.PF s U).length) 1 hDW (by omega)).1
  have hwk : Asm.limbs T'.mem c.up c.u1 = (c.sGF s U).w := by
    rw [Asm.limbs_upd (m := Y.mem) (j := (c.PF s U).length) (k := c.u1 - (c.PF s U).length)
      (by omega)
      (fun i hi hi2 => rk (c.up + 8 * i) 8
        (hext.held (huh.sub (by omega) (by omega)))
        (by simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true] at hqlu hi2 ⊢; omega)), hmc.wk]
    show Mdl.upd _ _ (Asm.limbs T'.mem (c.up + 8 * (c.PF s U).length) (c.u1 - (c.PF s U).length)) = _
    rw [hz]
    simp only [Cx.sGF, stS]
    rw [sTF_one hbl hql3 hb1]
    have hr1' : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
        ((c.sFF s U).buf.take (c.PF s U).length)).1.length = (c.PF s U).length := hr1
    have e := upd_app_full (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length)
        ((c.sFF s U).buf.take (c.PF s U).length)).1 ((c.sFF s U).w.drop (c.PF s U).length)
      (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).1 hX
    rw [hr1'] at e
    exact e
  have hmcT : McF R c s L' b' T'.mem j Z U qv (c.sGF s U) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun _ _ h => ws_up h (by omega) (by omega))
      (fun _ _ _ h => ws_up0 h (by omega) (by omega))
      (by simp only [win, outside_cons, outside_nil, and_true] at hqlu ⊢; omega)
      (by unfold Apart at hus ⊢; omega)
      (by unfold Apart at huv ⊢; omega)
      (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ win Y 4136 40 ++ [(c.up + 8 * (c.PF s U).length,
        c.up + 8 * (c.PF s U).length + 8 * (c.u1 - (c.PF s U).length))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true] at hqlu ⊢; omega) (by omega) (by omega))
  have hpcT : T'.rip = BitVec.ofNat 64 rFD5W := by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]
  have hspT : T'.regs 4 = s.regs 4 - 392#64 := by rw [f1, hsp]; bv_omega
  have h5T : T'.regs 5 = s.regs 4 - 8#64 := f2.trans h5
  have h14T : T'.regs 14 = s.regs 14 := f3.trans h14
  have hx15T : T'.xmm 15 = 0#128 := f4.trans hx15
  have hB1 : Box (McF R c s L' b' T'.mem j Z U qv (c.sGF s U)) := ⟨hmcT⟩
  have hB2 : Box (V3F c s T'.mem qv (c.PF s U).length) := ⟨hv4.frame hMF hhi h0'⟩
  have hfsT : T'.fsBase = s.fsBase := g1.trans hfs
  have hdfT : T'.df = false := g2.trans hdf
  clear hmcT hv4 hmc hmc0 hv40 hMF hLF rk kT kQ hval hinv hpre hcr hzc hz hY hwk hhi hcr0 f1 f2 f3 f4 g1 g2 hT
  janus64_run [hax] until [rJF6]
  refine k _ rfl ?sp ?r5 ?r14 hfsT (by dsimp only) ?x15 L' b' hB1.h hB2.h
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case sp => exact hspT
  case r5 => exact h5T
  case r14 => exact h14T
  case x15 => exact hx15T

end FvModexp.Amd64.Q.DivRec
