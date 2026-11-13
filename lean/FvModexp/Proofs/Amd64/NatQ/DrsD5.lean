import FvModexp.Proofs.Amd64.NatQ.DrsD5R
import FvModexp.Proofs.Amd64.NatQ.DrsDG
import FvModexp.Proofs.Amd64.NatQ.DrsC5
import FvModexp.Proofs.Amd64.NatQ.DrsC6

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsD5.lean)
# `divRecursiveStep` (amd64), after the correction loop: `subVW(uu[ql:], uu[ql:], 1)` (natdiv.go:849)

`d5`: from the `CALL subVW` entry `Y` (`RSP = r - 400`, return `0x5f003f`; `Mc … (stS ql stF)` at the pre-call state `T`)
→ `subVW` (`SubVW.ens` on `LibDrs`, in place on `uu[ql:]`, `y = 1`) → its return `0x5f003f` (`rJ6`) with `Mc … stG`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

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
/-- the return site `0x5f003f` is admissible for `subVW`'s program -/
theorem raJ6 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments [SubVW.fn]).link impl) rJ6 := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := [SubVW.fn])
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0x7bf (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(uu[ql:], uu[ql:], 1)`** from its callee entry -/
theorem d5 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (Q : State → Prop) (T : State)
    (hmc0 : Mc R c s Lk bk T.mem j Z U qv (stS (c.P s j U).length (c.stF s j U)))
    (hv40 : V4 c s T.mem qv (c.P s j U).length)
    (Y : State) (hpc : Y.rip = BitVec.ofNat 64 SubVW.entry) (hsp : Y.regs 4 = s.regs 4 - 400#64)
    (h5 : Y.regs 5 = s.regs 4 - 8#64) (h14 : Y.regs 14 = s.regs 14) (hfs : Y.fsBase = s.fsBase)
    (hdf : Y.df = false) (hx15 : Y.xmm 15 = 0#128)
    (h0 : Y.regs 0 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length))
    (h3 : Y.regs 3 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length))
    (h1 : Y.regs 1 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length))
    (h7 : Y.regs 7 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length))
    (h6 : Y.regs 6 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length))
    (h8 : Y.regs 8 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length)) (h9 : Y.regs 9 = 1#64)
    (hFR : MemFrame T.mem Y.mem (isR s)) (hreg0 : Y.mem.regions = T.mem.regions)
    (hra : Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rJ6)
    (M0 : Memory) (hwE : Asm.limbs M0 (c.uuP j) (c.uuL j) = (c.stF s j U).w)
    (hb1 : (Mdl.subVV ((c.stF s j U).w.take (c.P s j U).length)
      ((c.stF s j U).buf.take (c.P s j U).length)).2 = 1)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rJ6 → T'.regs 4 = s.regs 4 - 392#64 → T'.regs 5 = s.regs 4 - 8#64 →
      T'.regs 14 = s.regs 14 → T'.fsBase = s.fsBase → T'.df = false → T'.xmm 15 = 0#128 →
      ∀ (L' : List (Nat × Nat)) (b' : Nat),
      Mc R c s L' b' T'.mem j Z U qv (c.stG s j U) → V4 c s T'.mem qv (c.P s j U).length →
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
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame T.mem Y.mem (is1 s) := hFR.mono fun x n ho => by
    simp only [isR, is1, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := Mc.own1 hmc0 hF1 hreg0
  have hv4 := V4.own1 hv40 hF1 h0'
  have hspn : (Y.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : Callees.CallEnvND R Lk Y 4136 40 := by
    obtain ⟨g1, g2, g3, -, g5, g6, g7, g8, -, g10, g11, g12⟩ :=
      Ev.callEnv (k := 4136) (a := 40) hcr hmc.ev hspn h14 hfs (by omega) (by omega)
    exact ⟨g1, g2, g3, g5, g6, g7, g8, g10, g11, g12⟩
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
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 3) (Y.regs 1) (Y.regs 7)
    (Y.regs 6) (Y.regs 8) (Y.regs 9)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?xz, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra => rw [show (Y.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raJ6 impl hap
  case xz => rw [h6, h3]
  case pre =>
    have e07 : Y.regs 0 = Y.regs 7 := by rw [h0, h7]
    unfold SubVW.Pre
    rw [if_pos e07]
    rw [h0, h3, h1, h7, h8, t0, t1, t2, ep]
    simp only [Cx.uuL, Cx.uuC] at hulc ⊢
    refine ⟨hce', by omega, by omega, by omega, by omega, fun _ => ⟨by omega,
      hext.held (huh.sub (by omega) (by omega)), by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega),
      by omega⟩, ?_, ?_, ?_, by omega, hext.held (huh.sub (by omega) (by omega)), ?_, Or.inl trivial,
      by rw [h14]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h14, hfs]; unfold Apart at hug hutl ⊢; (try simp only [grd, tls]); omega
    · rw [hXacc]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h3, h7, h9, t0, t1, t6] at hq
  obtain ⟨g1, g2, -, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = Y.mem.regions := hrgT
  rw [h14] at hinv
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.uuP j + 8 * (c.P s j U).length,
        c.uuP j + 8 * (c.P s j U).length + 8 * (c.uuL j - (c.P s j U).length))] →
      T'.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have t0u := hcr.t0u
  have kT : T'.mem.readLE c.t0 (8 * (c.q0 s j U).length) = Y.mem.readLE c.t0 (8 * (c.q0 s j U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true]; omega
  have kQ : T'.mem.readLE qv (8 * (3 * c.vl)) = Y.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h (by have := hrg.w; exact this) ?_
    have := hrg.u; unfold Apart at this; simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true]; omega
  -- `uu` after the call
  have hql3 : (c.P s j U).length ≤ 3 * c.vl := by omega
  have hqlu : (c.P s j U).length ≤ c.uuL j := Nat.le_trans hPl (uuL_ge hjm hcr.vu1)
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
  have hz := (Asm.subVW_model Y.mem T'.mem _ _ _ 1 _ (by omega) hval rfl).1
  rw [hY] at hz
  have hX := (Mdl.subVW_spec ((c.stF s j U).w.drop (c.P s j U).length) 1 hDW (by omega)).1
  have hwk : Asm.limbs T'.mem (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) = (c.stG s j U).w := by
    rw [Asm.limbs_upd (m := Y.mem) (j := (c.P s j U).length) (k := c.uuL j - (c.P s j U).length)
      (by simp only [Cx.uuL] at hqlu ⊢; omega)
      (fun i hi hi2 => rk (c.up + 8 * (j - c.vl / 2) + 8 * i) 8
        (hext.held (huh.sub (by simp only [Cx.uuL] at hqlu; omega) (by simp only [Cx.uuL] at hqlu; omega)))
        (by simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu hi2 ⊢; omega)), hmc.wk]
    show Mdl.upd _ _ (Asm.limbs T'.mem (c.uuP j + 8 * (c.P s j U).length) (c.uuL j - (c.P s j U).length)) = _
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
  have hmcT : Mc R c s L' b' T'.mem j Z U qv (c.stG s j U) :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun _ _ h => ws_up h (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega))
      (fun _ _ _ h => ws_up0 h (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega))
      (by simp only [win, Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega)
      (by unfold Apart at hus ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart at huv ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart at hqu ⊢; simp only [Cx.uuP, Cx.uuL] at hqlu ⊢; omega)
      (by unfold Apart; simp only [Cx.uuP]; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ win Y 4136 40 ++ [(c.uuP j + 8 * (c.P s j U).length,
        c.uuP j + 8 * (c.P s j U).length + 8 * (c.uuL j - (c.P s j U).length))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, Cx.uuP, Cx.uuL, outside_cons, outside_nil, and_true] at hqlu ⊢; omega) (by omega) (by omega))
  exact k T' (by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]) (by rw [f1, hsp]; bv_omega) (f2.trans h5)
    (f3.trans h14) (g1.trans hfs) (g2.trans hdf) (f4.trans hx15) L' b' hmcT (hv4.frame hMF hhi h0')

end FvModexp.Amd64.Q.DivRec
