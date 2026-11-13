import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFC5R
import FvModexp.Proofs.Arm64.NatQ.DrsC5

/-! (Q-form copy of Arm64/Nat/DrsFC5.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final correction loop: `subVW(qhatv[s:], qhatv[s:], c)` (natdiv.go:874)

`c5F`: the call (`vwSum`) → its return `0x1babb0` with `BxF` at `stC` (`corrSub`'s then-branch). Adapted from DrsC5.
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
/-- **`subVW(qhatv[s:], qhatv[s:], c)`** from its call state -/
theorem c5F (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop)
    (Y : State) (hpc : Y.pc = BitVec.ofNat 64 SubVW.entry) (h30 : Y.regs 30 = BitVec.ofNat 64 rFA)
    (h0 : Y.regs 0 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)))
    (h1 : Y.regs 1 = BitVec.ofNat 64 ((c.PF s U).length - c.vl / 2 + 1))
    (h2 : Y.regs 2 = BitVec.ofNat 64 (3 * c.vl - c.vl / 2 + 1)) (h3 : Y.regs 3 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)))
    (h4 : Y.regs 4 = BitVec.ofNat 64 ((c.PF s U).length - c.vl / 2 + 1))
    (h5 : Y.regs 5 = BitVec.ofNat 64 (3 * c.vl - c.vl / 2 + 1))
    (h6 : Y.regs 6 = BitVec.ofNat 64 (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2)
    (hlt : c.vl / 2 - 1 < (c.PF s U).length)
    (hbx : BxF R c s Lk bk Y j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)))
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rFA → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      BxF R c s L' b' T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, -, huh, huw, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjB := hmc.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hsp := hbx.sp; have h28 := hbx.r28
  have hspn : Y.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk Y 4144 40 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨g1, g2, -, g4, g5, g6, g7, -⟩ := hce'
  have hPl : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hrw := hrg.w
  simp only [win, outside_cons, outside_nil, and_true] at hrw
  have hqal := hmc.qal
  -- the slice `qhatv[s:len(qhatv)]`
  have ea : c.vl / 2 - 1 + ((c.PF s U).length - c.vl / 2 + 1) = (c.PF s U).length := by omega
  have hcy : (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 ≤ 1 := by
    exact subVVc_le1 _ _ 0 (by omega)
  have t0 := tN (by omega : qv + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t1 := tN (by omega : (c.PF s U).length - c.vl / 2 + 1 < 2 ^ 64)
  have t2 := tN (by omega : 3 * c.vl - c.vl / 2 + 1 < 2 ^ 64)
  have t6 := tN (by omega : (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 < 2 ^ 64)
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 1) (Y.regs 2) (Y.regs 3)
    (Y.regs 4) (Y.regs 5) (Y.regs 6)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?xz, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 rFA : BitVec 64).toNat = rFA := by decide
    rw [h30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case xz => rw [h4, h1]
  case pre =>
    have e03 : Y.regs 0 = Y.regs 3 := by rw [h0, h3]
    unfold SubVW.Pre
    rw [if_pos e03]
    rw [h0, h1, h2, h3, h5, t0, t1, t2]
    refine ⟨⟨g1, g2, g4, g5, g6, g7⟩, by omega, by omega, by omega, by omega, fun _ => ⟨by omega,
      hrg.h.sub (by omega) (by omega), Memory.accessible_mono _ hqa (by omega) (by omega), by omega⟩, ?_, ?_, ?_,
      by omega, hrg.h.sub (by omega) (by omega), ?_, Or.inl rfl, by rw [h28]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h28]; have := hrg.g; unfold Apart at this ⊢; simp only [grd] at this; omega
    · exact Memory.accessible_weaken _ (Memory.accessible_mono _ hqa (by omega) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h1, h3, h6, t0, t1, t6] at hq
  obtain ⟨-, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T.mem.regions = Y.mem.regions := hrgT
  rw [h28] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(qv + 8 * (c.vl / 2 - 1), qv + 8 * (c.vl / 2 - 1) + 8 * ((c.PF s U).length - c.vl / 2 + 1))] →
      T.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have ht0 := hrg.t0
  have hu := hrg.u
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have kT : T.mem.readLE c.t0 (8 * (c.qF s U).length) = Y.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at ht0; simp only [outside_cons, outside_nil, and_true]; omega
  have kW : T.mem.readLE c.up (8 * c.u1) = Y.mem.readLE c.up (8 * c.u1) :=
    rk _ _ (hext.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
      (by unfold Apart at hu; simp only [outside_cons, outside_nil, and_true]; omega)
  -- the buffer
  have hbf : Asm.limbs T.mem qv (3 * c.vl) = (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb).buf := by
    have hz := (Asm.subVW_model Y.mem T.mem (qv + 8 * (c.vl / 2 - 1)) (qv + 8 * (c.vl / 2 - 1))
      ((c.PF s U).length - c.vl / 2 + 1) _ _ (by omega) hval rfl).1
    rw [Asm.limbs_upd (m := Y.mem) (j := c.vl / 2 - 1) (k := (c.PF s U).length - c.vl / 2 + 1) (by omega)
      (fun i hi hi2 => rk _ _ (hrg.h.sub (by omega) (by omega)) (hrg.w.of_sub (by omega) (by omega))
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hz,
      ← Asm.sl_limbs Y.mem qv (3 * c.vl) (c.vl / 2 - 1) _ (by omega), hmc.bf]
    have ek : (c.PF s U).length - c.vl / 2 + 1 = (c.PF s U).length - (c.vl / 2 - 1) := by omega
    rw [ek]
    simp only [stC, stV, stQ, Mdl.corrSub, if_pos hlt]
  have hloc := hmc.qloc.out
  have hsub : ∀ x n, Outside x n [(qv, qv + 8 * (3 * c.vl))] →
      Outside x n [(qv + 8 * (c.vl / 2 - 1), qv + 8 * (c.vl / 2 - 1) + 8 * ((c.PF s U).length - c.vl / 2 + 1))] :=
    fun x n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have ap : ∀ {x n}, Apart qv (8 * (3 * c.vl)) x n →
      Apart x n (qv + 8 * (c.vl / 2 - 1)) (8 * ((c.PF s U).length - c.vl / 2 + 1)) := fun h => by
    unfold Apart at h ⊢; omega
  have hmcT : McF R c s L' b' T.mem j Z U qv (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun x n h => hsub _ _ (hloc.1 x n h)) (fun x n h1 h2 => hsub _ _ (hloc.2 x n h1 h2))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by have := hrg.st; unfold Apart at this ⊢; omega) (ap hrg.v)
      (ap (apSR hrg.u (by omega) (by omega))) (ap hrg.q)
      (by rw [limbs_congr kT]; exact hmc.qk) hbf (by rw [limbs_congr kW]; exact hmc.wk)
  have hhi : HiOut s (R.rt ++ winA Y 4144 40 ++
      [(qv + 8 * (c.vl / 2 - 1), qv + 8 * (c.vl / 2 - 1) + 8 * ((c.PF s U).length - c.vl / 2 + 1))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T (by rw [hT, h30]) L' b' ⟨f1.trans hsp, f2.trans h28, f3.trans hbx.r29, f4.trans hbx.r18, hmcT,
    hbx.v3.frame hMF hhi h0', ?_, hbx.hi, hbx.pos, hbx.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hbx.si

end FvModexp.Arm64.Q.DivRec
