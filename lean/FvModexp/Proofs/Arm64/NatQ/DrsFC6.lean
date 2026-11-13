import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFC5S
import FvModexp.Proofs.Arm64.NatQ.DrsC6
import FvModexp.Proofs.Arm64.NatQ.DrsWs

/-! (Q-form copy of Arm64/Nat/DrsFC6.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final correction loop: `addTo(u[s:], v[s:])` (natdiv.go:876)

`c6F`: the call (`atSum`) → its return `0x1babcc` with `BxF` at `Mdl.corrOnce stb` (adapted from DrsC6).
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`addTo(uu[s:], v[s:])`** from its call state -/
theorem c6F (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 addToA) (h30 : X.regs 30 = BitVec.ofNat 64 rFA2)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1))) (h1 : X.regs 1 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)))
    (h2 : X.regs 2 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1))) (h3 : X.regs 3 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)))
    (h4 : X.regs 4 = BitVec.ofNat 64 (c.vl - (c.vl / 2 - 1))) (h5 : X.regs 5 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)))
    (hbx : BxF R c s Lk bk X j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb))
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rFA2 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      BxF R c s L' b' T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, hvlc, hvc40, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, huh, huw, hug⟩,
    ⟨hva, hv48, hvh, hvw, -, -, -⟩, hqu, -, huv, -, ⟨-, -, -, -, hup8, -⟩, -, ⟨hus, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40; have hvu := hcr.vu1
  have hjB := hmc.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hsp := hbx.sp; have h28 := hbx.r28
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 4240 48 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hmc.ev.fr.accessible]
  simp only [win, outside_cons, outside_nil, and_true] at huw hvw
  have t0 := tN (by omega : c.up + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t1 := tN (by omega : c.u1 - (c.vl / 2 - 1) < 2 ^ 64)
  have t2 := tN (by omega : c.uc - (c.vl / 2 - 1) < 2 ^ 64)
  have t3 := tN (by omega : c.vp + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t4 := tN (by omega : c.vl - (c.vl / 2 - 1) < 2 ^ 64)
  refine ReachesRet.call_regions (atSum impl hap R hmv bk Lk (X.regs 0) (X.regs 1) (X.regs 2) (X.regs 3)
    (X.regs 4) (X.regs 5)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 rFA2 : BitVec 64).toNat = rFA2 := by decide
    rw [h30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case pre =>
    rw [h0, h1, h2, h3, h4, t0, t1, t2, t3, t4]
    refine ⟨hce', by omega, by omega, by omega, fun _ => ⟨by omega, hext.held (huh.sub (by omega) (by omega)),
      by rw [hXacc]; exact Memory.accessible_mono _ hua (by omega) (by omega), by omega⟩, ?_, by omega,
      by rw [hXacc]; exact Memory.accessible_mono _ hva (by omega) (by omega), by omega,
      hext.held (hvh.sub (by omega) (by omega)), ?_, fun _ => ?_, ?_, by rw [h28]; exact hmc.ev.inv⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · unfold Apart at huv ⊢; omega
    · rw [h28]; unfold Apart at hug ⊢; omega
  rw [h0, h1, h3, h4, t0, t1, t3, t4] at hq
  obtain ⟨hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T.mem.regions = X.mem.regions := hrgT
  rw [h28] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.up + 8 * (c.vl / 2 - 1), c.up + 8 * (c.vl / 2 - 1) + 8 * (c.u1 - (c.vl / 2 - 1)))] →
      T.mem.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have t0u := hcr.t0u
  have kT : T.mem.readLE c.t0 (8 * (c.qF s U).length) = X.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : T.mem.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h hrg.w ?_
    have := hrg.u; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  -- the remainder window `uu = u[j-B:u1]` after the call
  have hzv : Asm.limbs T.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) =
      Mdl.addTo (Asm.limbs X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)))
        (Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - (c.vl / 2 - 1))) :=
    Asm.addTo_model X.mem T.mem _ _ _ _ (by omega) hval
  have hwX : Asm.limbs X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) =
      (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb).w.drop (c.vl / 2 - 1) := by
    rw [← hmc.wk, Asm.limbs_drop]
  have hvX : Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - (c.vl / 2 - 1)) = (c.V s).drop (c.vl / 2 - 1) := by
    show _ = (Asm.limbs s.mem c.vp c.vl).drop _
    rw [Asm.limbs_drop]
    exact limbs_congr (rd_sub hmc.bd.vk (by omega) (by omega))
  have hwk : Asm.limbs T.mem c.up c.u1 =
      (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb).w := by
    rw [Asm.limbs_upd (m := X.mem) (j := c.vl / 2 - 1) (k := c.u1 - (c.vl / 2 - 1)) (by omega)
      (fun i hi hi2 => rk _ _ (hext.held (huh.sub (by omega) (by omega))) (by
        simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hmc.wk]
    rw [hzv, hwX, hvX]
    rfl
  have hmcT : McF R c s L' b' T.mem j Z U qv (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun _ _ h => ws_up h (by omega) (by omega))
      (fun _ _ _ h => ws_up0 h (by omega) (by omega))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hus ⊢; omega) (by unfold Apart at huv ⊢; omega) (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ winA X 4240 48 ++ [(c.up + 8 * (c.vl / 2 - 1), c.up + 8 * (c.vl / 2 - 1) + 8 * (c.u1 - (c.vl / 2 - 1)))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T (by rw [hT, h30]) L' b' ⟨f1.trans hsp, f2.trans h28, f3.trans hbx.r29, f4.trans hbx.r18, hmcT,
    hbx.v3.frame hMF hhi h0', ?_, hbx.hi, hbx.pos, hbx.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hbx.si

end FvModexp.Arm64.Q.DivRec
