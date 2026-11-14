import FvModexp.Proofs.Arm64.Nat.DrsSegD
import FvModexp.Proofs.Arm64.Nat.DrsCE
import FvModexp.Proofs.Common.DrsCorrVal
/-!
# `divRecursiveStep` (arm64), correction loop: `subVW(qhat, qhat, 1)` (natdiv.go:837)
`c3`: from the `CALL subVW` state (`0x1ba770`, `Bx … stb stb`) → `subVW` (`SubVW.ens` on `LibDrs`, in place) → its
return `0x1ba774` with `Bx … stb (stQ stb)` (model: `qhat := (Mdl.subVW qhat 1).1`).
-/
set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(qhat, qhat, 1)`** from its call state -/
theorem c3 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop)
    (Y : State) (hpc : Y.pc = BitVec.ofNat 64 SubVW.entry) (h30 : Y.regs 30 = BitVec.ofNat 64 0x1ba774)
    (h0 : Y.regs 0 = BitVec.ofNat 64 c.t0) (h1 : Y.regs 1 = BitVec.ofNat 64 (c.q0 s j U).length)
    (h2 : Y.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h3 : Y.regs 3 = BitVec.ofNat 64 c.t0)
    (h4 : Y.regs 4 = BitVec.ofNat 64 (c.q0 s j U).length) (h5 : Y.regs 5 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h6 : Y.regs 6 = 1#64) (hbx : Bx R c s Lk bk Y j Z U qv i stb stb)
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 0x1ba774 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      Bx R c s L' b' T j Z U qv i stb (stQ stb) → ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, -, huh, huw, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hsp := hbx.sp; have h28 := hbx.r28
  have hspn : Y.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk Y 4144 40 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨g1, g2, -, g4, g5, g6, g7, -⟩ := hce'
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have ht0w := hcr.t0w
  have ht0g := hcr.t0g
  have ht0al := hcr.t0al; have ht048 := hcr.t048
  have ht0acc : Y.mem.accessible c.t0 (8 * (c.vl / 2 + 1)) true = true := by
    rw [hmc.ev.fr.accessible]; exact hcr.t0acc
  have ht0h : Held R Lk c.t0 (8 * (c.vl / 2 + 1)) := hmc.ev.ext.held hcr.t0h
  simp only [win, outside_cons, outside_nil, and_true] at ht0w
  have t0 := tN (by omega : c.t0 < 2 ^ 64)
  have t1 := tN (by omega : (c.q0 s j U).length < 2 ^ 64)
  have t2 := tN (by omega : c.vl / 2 + 1 < 2 ^ 64)
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 1) (Y.regs 2) (Y.regs 3)
    (Y.regs 4) (Y.regs 5) (Y.regs 6)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?xz, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 0x1ba774 : BitVec 64).toNat = 0x1ba774 := by decide
    rw [h30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case xz => rw [h4, h1]
  case pre =>
    have e03 : Y.regs 0 = Y.regs 3 := by rw [h0, h3]
    unfold SubVW.Pre
    rw [if_pos e03]
    rw [h0, h1, h2, h3, h5, t0, t1, t2]
    refine ⟨⟨g1, g2, g4, g5, g6, g7⟩, hql, hql, by omega, by omega, fun _ => ⟨ht0al, ht0h.sub (Nat.le_refl _) (by omega),
      Memory.accessible_mono _ ht0acc (Nat.le_refl _) (by omega), by omega⟩, ?_, ?_, ?_, by omega,
      ht0h.sub (Nat.le_refl _) (by omega), ?_, Or.inl rfl, by rw [h28]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h28]; unfold Apart at ht0g ⊢; simp only [grd] at ht0g; omega
    · exact Memory.accessible_weaken _ (Memory.accessible_mono _ ht0acc (Nat.le_refl _) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h1, h3, h6, t0, t1] at hq
  obtain ⟨-, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T.mem.regions = Y.mem.regions := hrg
  rw [h28] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Outside x n [(c.t0, c.t0 + 8 * (c.q0 s j U).length)] →
      T.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg' := hmc.rg
  have kQ : T.mem.readLE qv (8 * (3 * c.vl)) = Y.mem.readLE qv (8 * (3 * c.vl)) :=
    rk _ _ hrg'.h hrg'.w (by
      have := hrg'.t0; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega)
  have t0u := hcr.t0u
  have kW : T.mem.readLE (c.up + 8 * (j - c.vl / 2)) (8 * (c.u1 - (j - c.vl / 2))) =
      Y.mem.readLE (c.up + 8 * (j - c.vl / 2)) (8 * (c.u1 - (j - c.vl / 2))) :=
    rk _ _ (hext.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega)) (by
      unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega)
  -- the new `qhat`
  have hqk : Asm.limbs T.mem c.t0 (c.q0 s j U).length = (stQ stb).qhat := by
    have := (Asm.subVW_model Y.mem T.mem c.t0 c.t0 (c.q0 s j U).length 1 _ (by decide) hval rfl).1
    rw [this, hmc.qk]
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hsub : ∀ x n, Outside x n [(c.t0, c.t0 + 8 * (c.vl / 2 + 1))] →
      Outside x n [(c.t0, c.t0 + 8 * (c.q0 s j U).length)] := fun x n h => by
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have ap : ∀ {x n}, Apart c.t0 (8 * (c.vl / 2 + 1)) x n → Apart x n c.t0 (8 * (c.q0 s j U).length) := fun h => by
    unfold Apart at h ⊢; omega
  have hmcT : Mc R c s L' b' T.mem j Z U qv (stQ stb) :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun x n h => hsub _ _ (hloc.1 x n h)) (fun x n h1 h2 => hsub _ _ (hloc.2 x n h1 h2))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by have := hcr.t0st; unfold Apart at this ⊢; omega) (ap hcr.t0v)
      (ap (apSR hcr.t0u (by omega) (by omega))) (ap hcr.t0q) (ap (apSR hcr.t0u (Nat.le_refl _) (by omega)))
      hqk (by rw [limbs_congr kQ]; exact hmc.bf) (by rw [limbs_congr kW]; exact hmc.wk)
  have hhi : HiOut s (R.rt ++ winA Y 4144 40 ++ [(c.t0, c.t0 + 8 * (c.q0 s j U).length)]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T (by rw [hT, h30]) L' b' ⟨f1.trans hsp, f2.trans h28, f3.trans hbx.r29, f4.trans hbx.r18, hmcT,
    hbx.v4.frame hMF hhi h0', ?_, hbx.hi, hbx.pos, hbx.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hbx.si

end FvModexp.Arm64.DivRec
