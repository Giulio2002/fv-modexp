import FvModexp.Proofs.Amd64.NatQ.DrsFC5S
import FvModexp.Proofs.Amd64.NatQ.DrsC6

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC6.lean; adapted from Amd64/NatQ/DrsC6.lean)
# `divRecursiveStep` (amd64), final correction loop: `addTo(u[s:], v[s:])` (natdiv.go:877)

`c6F`: from the `CALL addTo` entry `X` (`RSP = r - 400`, return `0x5f0505`; `BxF … stb (stC …)` at the pre-call state
`T`) → `addTo` (`atSum`; window `win X 4232 48`; writes `u[s : u1]`) → its return `0x5f0505` with
`BxF … stb (corrOnce V s ql stb)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
/-- the return site `0x5f0505` is admissible for `addTo`'s program -/
theorem raFA (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) rFA := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := AddTo.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0xc85 (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`addTo(u[s:], v[s:])`** (final loop) from its callee entry -/
theorem c6F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop) (T : State)
    (hby : BxF R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb))
    (X : State) (hpc : X.rip = BitVec.ofNat 64 addToC) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)))
    (h3 : X.regs 3 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)))
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1))) (h7 : X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)))
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.vl - (c.vl / 2 - 1))) (h8 : X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)))
    (hFR : MemFrame T.mem X.mem (isR s)) (hreg0 : X.mem.regions = T.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFA)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rFA → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      BxF R c s L' b' T' j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hmc0 := hby.mc
  have hcr := hmc0.cr
  have hpre := hcr.pre
  have hup8 : c.up % 8 = 0 := hpre.stl.2.2.2.2.1
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hua, hu48, huh, huw, hug⟩ := hpre.ua
  obtain ⟨hva, hv48, hvh, hvw, -, -, -⟩ := hpre.va
  have hv9 := hpre.v9.1; have hvc40 := hpre.vc40; have hvlc := hpre.vlc
  have hul := hpre.ulc; have huc := hpre.uc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40; have hvu := hcr.vu1
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame T.mem X.mem (is1F s) := hFR.mono fun x n ho => by
    simp only [isR, is1F, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := McF.own1 hmc0 hF1 hreg0
  have hv4X := V3F.own1 hby.v3 hF1 h0'
  have hsiX : X.mem.readLE ((s.regs 4).toNat - 184) 8 = i := by
    rw [hFR.readLE _ _ (by simp only [isR, outside_cons, outside_nil, and_true]; omega)]; exact hby.si
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 4232 48 := Ev.callEnv hcr hmc.ev hspn h14 hfs (by omega) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hmc.ev.fr.accessible]
  simp only [win, outside_cons, outside_nil, and_true] at huw hvw
  have hqu := hpre.qu; have huv := hpre.uv; have hus := hpre.su.1; have hutl := hpre.tl.2.1
  have t0 := tN (by omega : c.up + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t1 := tN (by omega : c.u1 - (c.vl / 2 - 1) < 2 ^ 64)
  have t2 := tN (by omega : c.uc - (c.vl / 2 - 1) < 2 ^ 64)
  have t3 := tN (by omega : c.vp + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t4 := tN (by omega : c.vl - (c.vl / 2 - 1) < 2 ^ 64)
  have t5 := tN (by omega : c.vc - (c.vl / 2 - 1) < 2 ^ 64)
  refine ReachesRet.call_regions (atSum impl hap R hmv bk Lk (X.regs 0) (X.regs 3) (X.regs 1) (X.regs 7)
    (X.regs 6) (X.regs 8)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, ⟨g1, g2, hq⟩⟩ hrgT => ?_)
  case ra => rw [show (X.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raFA impl hap
  case pre =>
    rw [h0, h3, h1, h7, h6, t0, t1, t2, t3, t4]
    refine ⟨hce', by omega, by omega, by omega, fun _ => ⟨by omega, hext.held (huh.sub (by omega) (by omega)),
      by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega), by omega⟩, ?_, by omega,
      by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hva (by omega) (by omega), by omega,
      hext.held (hvh.sub (by omega) (by omega)), ?_, fun _ => ?_, ?_, ?_, by rw [h14]; exact hmc.ev.inv⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · unfold Apart at huv ⊢; omega
    · rw [h14]; unfold Apart at hug ⊢; omega
    · rw [hfs]; unfold Apart at hutl ⊢; omega
  rw [h0, h3, h7, h6, t0, t1, t3, t4] at hq
  obtain ⟨hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = X.mem.regions := hrgT
  rw [h14] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.up + 8 * (c.vl / 2 - 1), c.up + 8 * (c.vl / 2 - 1) + 8 * (c.u1 - (c.vl / 2 - 1)))] →
      T'.mem.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Janus.Arm64.Memory.accessible_bound _ hqa
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have t0u := hcr.t0u
  have kT : T'.mem.readLE c.t0 (8 * (c.qF s U).length) = X.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : T'.mem.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h hrg.w ?_
    have := hrg.u; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  -- the remainder window `uu = u[j-B:u1]` after the call
  have hzv : Asm.limbs T'.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) =
      Mdl.addTo (Asm.limbs X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)))
        (Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - (c.vl / 2 - 1))) :=
    Asm.addTo_model X.mem T'.mem _ _ _ _ (by omega) hval
  have hwX : Asm.limbs X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) =
      (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb).w.drop (c.vl / 2 - 1) := by
    rw [← hmc.wk, Asm.limbs_drop]
  have hvX : Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - (c.vl / 2 - 1)) = (c.V s).drop (c.vl / 2 - 1) := by
    show _ = (Asm.limbs s.mem c.vp c.vl).drop _
    rw [Asm.limbs_drop]
    exact limbs_congr (rd_sub hmc.bd.vk (by omega) (by omega))
  have hwk : Asm.limbs T'.mem c.up c.u1 =
      (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb).w := by
    rw [Asm.limbs_upd (m := X.mem) (j := c.vl / 2 - 1) (k := c.u1 - (c.vl / 2 - 1)) (by omega)
      (fun i hi hi2 => rk _ _ (hext.held (huh.sub (by omega) (by omega))) (by
        simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hmc.wk]
    rw [hzv, hwX, hvX]
    rfl
  have hmcT : McF R c s L' b' T'.mem j Z U qv (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun _ _ h => ws_up h (by omega) (by omega)) (fun _ _ _ h => ws_up0 h (by omega) (by omega))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hus ⊢; omega) (by unfold Apart at huv ⊢; omega) (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ win X 4232 48 ++ [(c.up + 8 * (c.vl / 2 - 1), c.up + 8 * (c.vl / 2 - 1) + 8 * (c.u1 - (c.vl / 2 - 1)))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T' (by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]) L' b'
    ⟨by rw [f1, hsp]; bv_omega, f2.trans h5, f3.trans h14, g1.trans hfs, g2.trans hdf, f4.trans hx15, hmcT,
      hv4X.frame hMF hhi h0', ?_, hby.hi, hby.pos, hby.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hsiX

end FvModexp.Amd64.Q.DivRec
