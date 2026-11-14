import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC5.lean; adapted from Amd64/NatQ/DrsC5.lean)
# `divRecursiveStep` (amd64), final correction loop: `subVW(qhatv[s:], qhatv[s:], c)` (natdiv.go:875)

`c5F`: from the `CALL subVW` entry `Y` (`RSP = r - 400`, return `0x5f04d1`; `BxF … stb (stV V s (stQ stb))` at the
pre-call state `T`) → `subVW` (`vwSum`, in place on `qhatv[s:len(qhatv)]`, `y` = the `subVV` borrow) → its return
with `BxF … stb (stC V s ql stb)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
/-- the return site `0x5f04d1` is admissible for `subVW`'s program -/
theorem raWF2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments [SubVW.fn]).link impl) rFW2 := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := [SubVW.fn])
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0xc51 (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(qhatv[s:], qhatv[s:], c)`** from its callee entry -/
theorem c5F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop) (T : State)
    (hby : BxF R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)))
    (hlt : c.vl / 2 - 1 < (c.PF s U).length)
    (Y : State) (hpc : Y.rip = BitVec.ofNat 64 SubVW.entry) (hsp : Y.regs 4 = s.regs 4 - 400#64)
    (h5 : Y.regs 5 = s.regs 4 - 8#64) (h14 : Y.regs 14 = s.regs 14) (hfs : Y.fsBase = s.fsBase)
    (hdf : Y.df = false) (hx15 : Y.xmm 15 = 0#128)
    (h0 : Y.regs 0 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)))
    (h3 : Y.regs 3 = BitVec.ofNat 64 ((c.PF s U).length - (c.vl / 2 - 1)))
    (h1 : Y.regs 1 = BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1))) (h7 : Y.regs 7 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)))
    (h6 : Y.regs 6 = BitVec.ofNat 64 ((c.PF s U).length - (c.vl / 2 - 1)))
    (h8 : Y.regs 8 = BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)))
    (h9 : Y.regs 9 = BitVec.ofNat 64 (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2)
    (hFR : MemFrame T.mem Y.mem (isR s)) (hreg0 : Y.mem.regions = T.mem.regions)
    (hra : Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rFW2)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rFW2 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      BxF R c s L' b' T' j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q := by
  have hmc0 := hby.mc
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame T.mem Y.mem (is1F s) := hFR.mono fun x n ho => by
    simp only [isR, is1F, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := McF.own1 hmc0 hF1 hreg0
  have hv4Y := V3F.own1 hby.v3 hF1 h0'
  have hsiY : Y.mem.readLE ((s.regs 4).toNat - 184) 8 = i := by
    rw [hFR.readLE _ _ (by simp only [isR, outside_cons, outside_nil, and_true]; omega)]; exact hby.si
  have hspn : (Y.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : Callees.CallEnvND R Lk Y 4136 40 := by
    obtain ⟨g1, g2, g3, -, g5, g6, g7, g8, -, g10, g11, g12⟩ :=
      Ev.callEnv (k := 4136) (a := 40) hcr hmc.ev hspn h14 hfs (by omega) (by omega)
    exact ⟨g1, g2, g3, g5, g6, g7, g8, g10, g11, g12⟩
  have hPl : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Janus.Arm64.Memory.accessible_bound _ hqa
  have hrw := hrg.w
  simp only [win, outside_cons, outside_nil, and_true] at hrw
  have hqal := hmc.qal
  have hcy : (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 ≤ 1 :=
    subVVc_le1 _ _ 0 (by omega)
  have t0 := tN (by omega : qv + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t1 := tN (by omega : (c.PF s U).length - (c.vl / 2 - 1) < 2 ^ 64)
  have t2 := tN (by omega : 3 * c.vl - (c.vl / 2 - 1) < 2 ^ 64)
  have t6 := tN (by omega : (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 < 2 ^ 64)
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 3) (Y.regs 1) (Y.regs 7)
    (Y.regs 6) (Y.regs 8) (Y.regs 9)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?xz, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra => rw [show (Y.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raWF2 impl hap
  case xz => rw [h6, h3]
  case pre =>
    have e07 : Y.regs 0 = Y.regs 7 := by rw [h0, h7]
    unfold SubVW.Pre
    rw [if_pos e07]
    rw [h0, h3, h1, h7, h8, t0, t1, t2]
    refine ⟨hce', by omega, by omega, by omega, by omega, fun _ => ⟨by omega,
      hrg.h.sub (by omega) (by omega), Janus.Arm64.Memory.accessible_mono _ hqa (by omega) (by omega), by omega⟩,
      ?_, ?_, ?_, by omega, hrg.h.sub (by omega) (by omega), ?_, Or.inl rfl, by rw [h14]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h14, hfs]; have h1' := hrg.g; have h2' := hrg.fs; unfold Apart at h1' h2' ⊢
      simp only [grd, tls] at h1' h2'; omega
    · exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hqa (by omega) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h3, h7, h9, t0, t1, t6] at hq
  obtain ⟨g1, g2, -, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = Y.mem.regions := hrgT
  rw [h14] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(qv + 8 * (c.vl / 2 - 1), qv + 8 * (c.vl / 2 - 1) + 8 * ((c.PF s U).length - (c.vl / 2 - 1)))] →
      T'.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have ht0 := hrg.t0
  have hu := hrg.u
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have kT : T'.mem.readLE c.t0 (8 * (c.qF s U).length) = Y.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at ht0; simp only [outside_cons, outside_nil, and_true]; omega
  have kW : T'.mem.readLE c.up (8 * c.u1) = Y.mem.readLE c.up (8 * c.u1) :=
    rk _ _ (hext.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
      (by unfold Apart at hu; simp only [outside_cons, outside_nil, and_true]; omega)
  -- the buffer
  have hbf : Asm.limbs T'.mem qv (3 * c.vl) = (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb).buf := by
    have hz := (Asm.subVW_model Y.mem T'.mem (qv + 8 * (c.vl / 2 - 1)) (qv + 8 * (c.vl / 2 - 1))
      ((c.PF s U).length - (c.vl / 2 - 1)) _ _ (by omega) hval rfl).1
    rw [Asm.limbs_upd (m := Y.mem) (j := c.vl / 2 - 1) (k := (c.PF s U).length - (c.vl / 2 - 1)) (by omega)
      (fun i hi hi2 => rk _ _ (hrg.h.sub (by omega) (by omega)) (hrg.w.of_sub (by omega) (by omega))
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hz,
      ← Asm.sl_limbs Y.mem qv (3 * c.vl) (c.vl / 2 - 1) _ (by omega), hmc.bf]
    simp only [stC, stV, stQ, Mdl.corrSub, if_pos hlt]
  have hloc := hmc.qloc.out
  have hsub : ∀ x n, Outside x n [(qv, qv + 8 * (3 * c.vl))] →
      Outside x n [(qv + 8 * (c.vl / 2 - 1), qv + 8 * (c.vl / 2 - 1) + 8 * ((c.PF s U).length - (c.vl / 2 - 1)))] :=
    fun x n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have ap : ∀ {x n}, Apart qv (8 * (3 * c.vl)) x n →
      Apart x n (qv + 8 * (c.vl / 2 - 1)) (8 * ((c.PF s U).length - (c.vl / 2 - 1))) := fun h => by
    unfold Apart at h ⊢; omega
  have hmcT : McF R c s L' b' T'.mem j Z U qv (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun x n h => hsub _ _ (hloc.1 x n h)) (fun x n h1 h2 => hsub _ _ (hloc.2 x n h1 h2))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by have := hrg.st; unfold Apart at this ⊢; omega) (ap hrg.v)
      (ap (apR hrg.u (by omega) (by omega))) (ap hrg.q)
      (by rw [limbs_congr kT]; exact hmc.qk) hbf (by rw [limbs_congr kW]; exact hmc.wk)
  have hhi : HiOut s (R.rt ++ win Y 4136 40 ++
      [(qv + 8 * (c.vl / 2 - 1), qv + 8 * (c.vl / 2 - 1) + 8 * ((c.PF s U).length - (c.vl / 2 - 1)))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T' (by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]) L' b'
    ⟨by rw [f1, hsp]; bv_omega, f2.trans h5, f3.trans h14, g1.trans hfs, g2.trans hdf, f4.trans hx15, hmcT,
      hv4Y.frame hMF hhi h0', ?_, hby.hi, hby.pos, hby.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hsiY

end FvModexp.Amd64.Q.DivRec
