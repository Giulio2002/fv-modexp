import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFD4.lean; adapted from Amd64/NatQ/DrsD4.lean)
# `divRecursiveStep` (amd64), final block: `c := subVV(u[:ql], u[:ql], qhatv)` (natdiv.go:882)

`d4F`: from the `subVV.abi0` entry `X` (`RSP = r - 400`, return `0x5f05bf`) → `subVV.abi0` (`svvD`) → the re-entry
sequence (`XORPS X15`; `MOVQ FS:-8, R14`) → `0x5f05cc` with `McF` at `stS ql st` (`u[:ql] -= qhatv`) and the borrow at
`r - 320`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)
open FvModexp.Amd64.Callees (VVLPre SubVVLQ SubVVHyp subVVHyp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`c := subVV(uu[:ql], uu[:ql], qhatv)`** from its callee entry, through the re-entry sequence -/
theorem d4F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (st : Mdl.St) (Q : State → Prop) (T : State) (hmc0 : McF R c s Lk bk T.mem j Z U qv st)
    (hv4 : V3F c s T.mem qv (c.PF s U).length)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 subVVA) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false)
    (hF : MemFrame T.mem X.mem (isA s)) (hreg : X.mem.regions = T.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFD4)
    (ez : X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.up)
    (en : X.mem.readLE ((s.regs 4).toNat - 384) 8 = (c.PF s U).length)
    (ex : X.mem.readLE ((s.regs 4).toNat - 368) 8 = c.up) (ey : X.mem.readLE ((s.regs 4).toNat - 344) 8 = qv)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rFD5 → T'.regs 4 = s.regs 4 - 392#64 → T'.regs 5 = s.regs 4 - 8#64 →
      T'.regs 14 = s.regs 14 → T'.fsBase = s.fsBase → T'.df = false → T'.xmm 15 = 0#128 →
      McF R c s Lk bk T'.mem j Z U qv (stS (c.PF s U).length st) → V3F c s T'.mem qv (c.PF s U).length →
      T'.mem.readLE ((s.regs 4).toNat - 320) 8 =
        (Mdl.subVV (st.w.take (c.PF s U).length) (st.buf.take (c.PF s U).length)).2 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, hga, -, -, -, ⟨-, -, htg⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hua, hu48, huh, huw, hug⟩ := hpre.ua
  have hqu := hpre.qu; have huv := hpre.uv; have hus := hpre.su.1; have hutl := hpre.tl.2.1
  obtain ⟨hva, hv48, -, -, -, -, -⟩ := hpre.va
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hmc := McF.ownA hmc0 hF hreg
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 0 88 := Ev.callEnv hcr hmc.ev hspn h14 hfs (by omega) (by omega)
  obtain ⟨-, -, -, -, -, -, -, hLs, -, ⟨htlX, -, -⟩⟩ := hce'
  have hfa : (18446744073709551608 + X.fsBase.toNat) % 18446744073709551616 = X.fsBase.toNat - 8 := by
    have := htlX.base; omega
  have hfrd := htlX.readable
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Janus.Arm64.Memory.accessible_bound _ hqa
  have hrw := hrg.w
  simp only [win, outside_cons, outside_nil, and_true] at hrw huw
  have hPl := PF_len_le2 (c := c) (s := s) (U := U) (by omega)
  have hql3 : (c.PF s U).length ≤ 3 * c.vl := by omega
  have hqlu : (c.PF s U).length ≤ c.u1 := Nat.le_trans hPl (by have := hcr.vu1; omega)
  have huP : c.up + 8 * c.u1 ≤ c.up + 8 * c.ul := by omega
  have huP0 : c.up ≤ c.up := by omega
  -- the frame words, at `RSP`
  have ez' : X.mem.readLE ((X.regs 4).toNat + 8) 8 = c.up := by rw [hspn, show (s.regs 4).toNat - 400 + 8 = (s.regs 4).toNat - 392 by omega]; exact ez
  have en' : X.mem.readLE ((X.regs 4).toNat + 16) 8 = (c.PF s U).length := by rw [hspn, show (s.regs 4).toNat - 400 + 16 = (s.regs 4).toNat - 384 by omega]; exact en
  have ex' : X.mem.readLE ((X.regs 4).toNat + 32) 8 = c.up := by rw [hspn, show (s.regs 4).toNat - 400 + 32 = (s.regs 4).toNat - 368 by omega]; exact ex
  have ey' : X.mem.readLE ((X.regs 4).toNat + 56) 8 = qv := by rw [hspn, show (s.regs 4).toNat - 400 + 56 = (s.regs 4).toNat - 344 by omega]; exact ey
  have e80 : (X.regs 4).toNat + 80 = (s.regs 4).toNat - 320 := by omega
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF.accessible, hmc0.ev.fr.accessible]
  have hzacc : X.mem.accessible c.up (8 * (c.PF s U).length) true = true := by
    rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hua huP0 (by omega)
  have hpreV : VVLPre R bk Lk X := by
    unfold VVLPre Callees.VVPre
    rw [ez', en', ex', ey']
    refine ⟨⟨ez', en', ex', ey', by rw [hspn, hra]; decide, by omega,
        by rw [hXacc, hspn]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega),
        hzacc, Janus.Arm64.Memory.accessible_weaken _ hzacc,
        Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega)),
        Or.inl rfl, Or.inr ?_, ?_⟩, by rw [h14]; exact hmc.ev.inv,
      hext.held (huh.sub huP0 (by omega)), hout.of_sub (by omega) (by omega), ?_, ?_, ?_, ?_⟩
    · have := hrg.u; unfold Apart at this ⊢; omega
    · rw [hspn]; unfold Apart; omega
    · rw [h14]; unfold Apart at hug ⊢; omega
    · rw [h14]; unfold Apart at hga ⊢; omega
    · rw [hfs]; unfold Apart at hutl ⊢; omega
    · have htw := hpre.ce.2.2.2.2.2.2.2.2.2.2.2; rw [hfs]; unfold Apart at htw ⊢; omega
  refine ReachesRet.call_regions (svvD impl hap R bk Lk) hpc hpreV fun T' hT hq hrgT => ?_
  obtain ⟨junk, f, v, vh, mx, m, z, rfl, -, ⟨hval, hcar, hfr⟩, hinv, -, htls⟩ := hq
  simp only [ez', en', ex', ey', e80] at hval hcar hfr
  rw [h14] at hinv
  have hregm : m.regions = X.mem.regions := hrgT
  have hcar1 : m.readLE ((s.regs 4).toNat - 320) 8 ≤ 1 := by rw [hcar]; split <;> omega
  obtain ⟨hz1, hb1⟩ := Asm.subVV_model X.mem m c.up c.up qv (c.PF s U).length _ hcar1 hval
  have hWt : Asm.limbs X.mem c.up (c.PF s U).length = st.w.take (c.PF s U).length := by
    rw [← hmc.wk, Asm.limbs_take _ _ _ _ hqlu]
  have hBt : Asm.limbs X.mem qv (c.PF s U).length = st.buf.take (c.PF s U).length := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hql3]
  have hwk : Asm.limbs m c.up c.u1 = (stS (c.PF s U).length st).w := by
    rw [Asm.limbs_upd (m := X.mem) (j := 0) (k := (c.PF s U).length) (by omega)
      (fun i hi hi2 => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hqlu ⊢; omega)),
      Mdl.upd_zero, hmc.wk]
    simp only [Nat.mul_zero, Nat.add_zero, Asm.length_limbs]
    rw [hz1, hWt, hBt]
  -- the frame of the call in the `McF.callN` form
  have hF' : MemFrame X.mem m (R.rt ++ win X 0 88 ++ [(c.up, c.up + 8 * (c.PF s U).length)]) :=
    hfr.mono fun x n ho => by
      simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      rw [hspn] at ho; omega
  have hL' : LiveFrame X.mem m Lk [(c.up, c.up + 8 * (c.PF s U).length)] := ⟨fun x n hin ho => hfr.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ho ⊢
    rw [hspn] at this; omega)⟩
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.up, c.up + 8 * (c.PF s U).length)] → m.readLE x n = X.mem.readLE x n :=
    fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hF' hL' hh hw' ho
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have t0u := hcr.t0u
  have kT : m.readLE c.t0 (8 * (c.qF s U).length) = X.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : m.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h (by simp only [win, outside_cons, outside_nil, and_true]; omega) ?_
    have := hrg.u; unfold Apart at this
    simp only [outside_cons, outside_nil, and_true]; omega
  have hmcT : McF R c s Lk bk m j Z U qv (stS (c.PF s U).length st) :=
    McF.callN hmc hspn (by omega) (by omega) hF' hL' (LiveExt.refl R Lk) hinv hregm (Nat.le_refl _)
      (fun _ _ h => ws_up h huP0 (by omega)) (fun _ _ _ h => ws_up0 h huP0 (by omega))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hus ⊢; omega) (by unfold Apart at huv ⊢; omega)
      (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  -- the slots
  have o : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 320 ∨ (s.regs 4).toNat - 312 ≤ a) → (s.regs 4).toNat - 408 ≤ a →
      a + 8 ≤ (s.regs 4).toNat + 96 → m.readLE a 8 = X.mem.readLE a 8 := fun a h1 h2 h3 => hfr.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]; omega)
  have hv4m : V3F c s m qv (c.PF s U).length :=
    ⟨(by rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact hv4.s320),
      (by rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact hv4.s144),
      (by rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact hv4.s160)⟩
  have hcm : m.readLE ((s.regs 4).toNat - 320) 8 =
      (Mdl.subVV (st.w.take (c.PF s U).length) (st.buf.take (c.PF s U).length)).2 := by
    rw [← hWt, ← hBt]; exact hb1
  -- the re-entry sequence: `XORPS X15, X15; MOVQ FS:-8, R14`
  have htg' : m.readLE (X.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [htls, hfs]
    have e := Ev.tls hcr hmc.ev
    simp only [tls] at e
    rw [e]; simp only [regG] at htg; exact htg
  have hfrm : m.accessible (X.fsBase.toNat - 8) 8 false = true := by rw [hfr.accessible]; exact hfrd
  have hraX : X.mem.readLE (X.regs 4).toNat 8 = rFD4 := by rw [hspn]; exact hra
  have hB1 : Box (McF R c s Lk bk m j Z U qv (stS (c.PF s U).length st)) := ⟨hmcT⟩
  have hB2 : Box (V3F c s m qv (c.PF s U).length) := ⟨hv4m⟩
  clear hmcT hv4m hmc hmc0 hv4 hF' hL' rk kT kQ hval hcar hfr hinv hpre hcr
  janus64_run [hraX, htg', hfa, hfrm] until [rFD5]
  refine k _ rfl ?sp ?r5 ?r14 ?fs ?df ?x15 hB1.h hB2.h hcm
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, regs0, Nat.reduceEqDiff, ↓reduceIte, regSP]; rw [hsp]; bv_omega
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, regs0, Nat.reduceEqDiff, ↓reduceIte, regSP, regFP]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case fs => exact hfs
  case df => dsimp only
  case x15 => simp only [Janus.Amd64.Tactic.setXmmF_apply, ↓reduceIte]

end FvModexp.Amd64.Q.DivRec
