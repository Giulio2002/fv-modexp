import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsC5R
import FvModexp.Proofs.Arm64.NatQ.DrsC3
import FvModexp.Proofs.Arm64.Nat.AddTo
import FvModexp.Proofs.Arm64.NatQ.DrsWs

/-! (Q-form copy of Arm64/Nat/DrsC6.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), correction loop: `addTo(uu[s:], v[s:])` (natdiv.go:842)

`c6`: from the `CALL addTo` state (`0x1ba6e8`, `Bx … stb (stC V s ql stb)`) → `addTo` (`AddTo.ens` on `LibDrs`) → its
return `0x1ba6ec` with `Bx … stb (corrOnce V s ql stb)` (model: `w := upd w s (addTo w[s:] v[s:])`, `Mdl.addTo_mod`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

theorem addToA_eq : segAddr Extracted.program AddTo.fn = addToA := by decide

/-- `addTo` as a summary in `LibDrs` -/
theorem atSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibDrs.program.link impl) addToA
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, xp, xl, xc] ∧
        (CallEnv R L s 4240 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4240 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4240 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8 ∧
          R.inv b L (s.regs 28).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        (natVal s'.mem zp.toNat zl.toNat =
            (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
          ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
            R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
            MemFrame s.mem s'.mem (R.rt ++ winA s 4240 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
            LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have h := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc) (noExit_restrict hap AddTo.names)
    (codeIn_restrict_mono hap (sub_of_all (ms := LibDrs.names) (by decide)))
  rw [← LibDrs.eq_only, addToA_eq] at h
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`addTo(uu[s:], v[s:])`** from its call state -/
theorem c6 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 addToA) (h30 : X.regs 30 = BitVec.ofNat 64 0x1ba6ec)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1))) (h1 : X.regs 1 = BitVec.ofNat 64 (c.u1 - j + 1))
    (h2 : X.regs 2 = BitVec.ofNat 64 (c.uc - j + 1)) (h3 : X.regs 3 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)))
    (h4 : X.regs 4 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1)) (h5 : X.regs 5 = BitVec.ofNat 64 (c.vc - c.vl / 2 + 1))
    (hbx : Bx R c s Lk bk X j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb))
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 0x1ba6ec → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      Bx R c s L' b' T j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, hvlc, hvc40, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, huh, huw, hug⟩,
    ⟨hva, hv48, hvh, hvw, -, -, -⟩, hqu, -, huv, -, ⟨-, -, -, -, hup8, -⟩, -, ⟨hus, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
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
  have t0 := tN (by omega : c.up + 8 * (j - 1) < 2 ^ 64)
  have t1 := tN (by omega : c.u1 - j + 1 < 2 ^ 64)
  have t2 := tN (by omega : c.uc - j + 1 < 2 ^ 64)
  have t3 := tN (by omega : c.vp + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t4 := tN (by omega : c.vl - c.vl / 2 + 1 < 2 ^ 64)
  refine ReachesRet.call_regions (atSum impl hap R hmv bk Lk (X.regs 0) (X.regs 1) (X.regs 2) (X.regs 3)
    (X.regs 4) (X.regs 5)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 0x1ba6ec : BitVec 64).toNat = 0x1ba6ec := by decide
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
      Outside x n [(c.up + 8 * (j - 1), c.up + 8 * (j - 1) + 8 * (c.u1 - j + 1))] →
      T.mem.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have t0u := hcr.t0u
  have kT : T.mem.readLE c.t0 (8 * (c.q0 s j U).length) = X.mem.readLE c.t0 (8 * (c.q0 s j U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : T.mem.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h hrg.w ?_
    have := hrg.u; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  -- the remainder window `uu = u[j-B:u1]` after the call
  have hzv : Asm.limbs T.mem (c.up + 8 * (j - 1)) (c.u1 - j + 1) =
      Mdl.addTo (Asm.limbs X.mem (c.up + 8 * (j - 1)) (c.u1 - j + 1))
        (Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1)) :=
    Asm.addTo_model X.mem T.mem _ _ _ _ (by omega) hval
  have hwX : Asm.limbs X.mem (c.up + 8 * (j - 1)) (c.u1 - j + 1) =
      (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb).w.drop (c.vl / 2 - 1) := by
    rw [← hmc.wk, Asm.limbs_drop]
    exact limbs_eq2 (by omega) (by omega)
  have hvX : Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) = (c.V s).drop (c.vl / 2 - 1) := by
    show _ = (Asm.limbs s.mem c.vp c.vl).drop _
    rw [Asm.limbs_drop, show c.vl - (c.vl / 2 - 1) = c.vl - c.vl / 2 + 1 by omega]
    exact limbs_congr (rd_sub hmc.bd.vk (by omega) (by omega))
  have hwk : Asm.limbs T.mem (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) =
      (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb).w := by
    rw [Asm.limbs_upd (m := X.mem) (j := c.vl / 2 - 1) (k := c.u1 - j + 1) (by omega)
      (fun i hi hi2 => rk _ _ (hext.held (huh.sub (by omega) (by omega))) (by
        simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hmc.wk]
    rw [show c.up + 8 * (j - c.vl / 2) + 8 * (c.vl / 2 - 1) = c.up + 8 * (j - 1) by omega, hzv, hwX, hvX]
    rfl
  have hpn : c.up + 8 * (j - 1) + 8 * (c.u1 - j + 1) ≤ c.up + 8 * c.ul := by omega
  have hmcT : Mc R c s L' b' T.mem j Z U qv (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun _ _ h => ws_up h (Nat.le_add_right _ _) hpn) (fun _ _ _ h => ws_up0 h (Nat.le_add_right _ _) hpn)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hus ⊢; omega) (by unfold Apart at huv ⊢; omega) (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega) (by unfold Apart; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ winA X 4240 48 ++ [(c.up + 8 * (j - 1), c.up + 8 * (j - 1) + 8 * (c.u1 - j + 1))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T (by rw [hT, h30]) L' b' ⟨f1.trans hsp, f2.trans h28, f3.trans hbx.r29, f4.trans hbx.r18, hmcT,
    hbx.v4.frame hMF hhi h0', ?_, hbx.hi, hbx.pos, hbx.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hbx.si

end FvModexp.Arm64.Q.DivRec
