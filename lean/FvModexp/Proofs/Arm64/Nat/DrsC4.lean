import FvModexp.Proofs.Arm64.Nat.DrsC4R
import FvModexp.Proofs.Arm64.Nat.AsmCallees
import FvModexp.Proofs.Common.DivBasicMem

/-!
# `divRecursiveStep` (arm64), correction loop: `c := subVV(qhatv[:s], qhatv[:s], v[:s])` (natdiv.go:838)

`c4`: from `c4r`'s call state (`0x1ba7a4`, the nine argument words stored) → `subVV.abi0` (`SubVVSum` on `LibDrs`) → its
return `0x1ba7a8` with `Bx … stb (stV V s st)` and the borrow `c` at `SP'+80` (model: `buf := (subVV buf[:s] v[:s]).1 ++
buf[s:]`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the model after `qhatv[:s] -= v[:s]` -/
@[reducible] def stV (V : List Nat) (s0 : Nat) (st : Mdl.St) : Mdl.St :=
  { st with buf := (Mdl.subVV (st.buf.take s0) (V.take s0)).1 ++ st.buf.drop s0 }

/-- `subVV.abi0` in `LibDrs` with the runtime invariant carried over -/
theorem svvD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDrs.program.link impl) subVVA (VVLPre R b L) (SubVVLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [subVVfn]).link impl) (LibDrs.program.link impl) := by
    rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact SubVVHyp.live (Summary.of_codeIn c (subVVHyp impl hap)) R b L

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `Mc` across the argument stores (`isA`) -/
theorem Mc.ownA {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : Mc R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (isA s))
    (hreg : M'.regions = M.regions) : Mc R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hjm : j ≤ c.u1 - c.vl := by have := h.li.2.2.2.2.2.2.2; omega
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, isA, outside_cons, outside_nil, and_true]; omega)
      (by simp only [IOut, isA, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw),
    h.bs.frame hF3 (by simp only [BOut, isA, outside_cons, outside_nil, and_true]; omega), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s208,
      by rw [hF3.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s256⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (by omega) (by omega))]; exact h.wk,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.lk, h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc⟩

theorem ret0_r (X : State) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (fpsr : BitVec 32) (m : Memory)
    (i : Nat) (hi : i = 18 ∨ i = 28 ∨ i = 29) : (retState0 X junk f v fpsr m).regs i = X.regs i := by
  simp only [retState0, regs0, regPlatform, regG, regFP]
  rw [if_pos hi]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`c := subVV(qhatv[:s], qhatv[:s], v[:s])`** from its call state -/
theorem c4 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb st : Mdl.St) (Q : State → Prop) (T : State) (hbx : Bx R c s Lk bk T j Z U qv i stb st)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 subVVA) (h30 : X.regs 30 = BitVec.ofNat 64 0x1ba7a8)
    (hsp : X.sp = s.sp - 400#64) (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64)
    (h18 : X.regs 18 = s.regs 18) (hF : MemFrame T.mem X.mem (isA s)) (hreg : X.mem.regions = T.mem.regions)
    (ez : X.mem.readLE (s.sp.toNat - 392) 8 = qv) (en : X.mem.readLE (s.sp.toNat - 384) 8 = c.vl / 2 - 1)
    (ex : X.mem.readLE (s.sp.toNat - 368) 8 = qv) (ey : X.mem.readLE (s.sp.toNat - 344) 8 = c.vp)
    (k : ∀ T' : State, T'.pc = BitVec.ofNat 64 0x1ba7a8 →
      Bx R c s Lk bk T' j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) st) →
      T'.mem.readLE (s.sp.toNat - 320) 8 = (Mdl.subVV (st.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hmc0 := hbx.mc
  have hcr := hmc0.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, -, huh, huw, -⟩, ⟨hva, hv48, -, -, -, -, -⟩, -⟩ :=
    hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, hga, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hmc := Mc.ownA hmc0 hF hreg
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 0 88 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨-, -, -, -, -, -, hLs, -⟩ := hce'
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hrw := hrg.w
  simp only [win, outside_cons, outside_nil, and_true] at hrw huw
  have hs3 : c.vl / 2 - 1 ≤ 3 * c.vl := by omega
  -- the frame words, at `X.sp`
  have e8 : X.sp.toNat + 8 = s.sp.toNat - 392 := by omega
  have e16 : X.sp.toNat + 16 = s.sp.toNat - 384 := by omega
  have e32 : X.sp.toNat + 32 = s.sp.toNat - 368 := by omega
  have e56 : X.sp.toNat + 56 = s.sp.toNat - 344 := by omega
  have e80 : X.sp.toNat + 80 = s.sp.toNat - 320 := by omega
  have ez' : X.mem.readLE (X.sp.toNat + 8) 8 = qv := by rw [e8]; exact ez
  have en' : X.mem.readLE (X.sp.toNat + 16) 8 = c.vl / 2 - 1 := by rw [e16]; exact en
  have ex' : X.mem.readLE (X.sp.toNat + 32) 8 = qv := by rw [e32]; exact ex
  have ey' : X.mem.readLE (X.sp.toNat + 56) 8 = c.vp := by rw [e56]; exact ey
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF.accessible, hmc0.ev.fr.accessible]
  have hpre : VVLPre R bk Lk X := by
    unfold VVLPre
    rw [ez', en']
    refine ⟨?_, by rw [h28]; exact hmc.ev.inv, hrg.h.sub (Nat.le_refl _) (by omega),
      hout.of_sub (by omega) (by omega), ?_, ?_⟩
    · unfold VVPre
      rw [ez', en', ex', ey']
      refine ⟨ez', en', ex', ey', by rw [h30]; decide, by rw [h30]; decide, by rw [hspn]; omega, by omega,
        by rw [hXacc]; exact Memory.accessible_mono _ hw (by omega) (by omega),
        Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega),
        Memory.accessible_weaken _ (Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega)),
        by rw [hXacc]; exact Memory.accessible_mono _ hva (Nat.le_refl _) (by omega), Or.inl rfl, Or.inr ?_, ?_⟩
      · have := hrg.v; unfold Apart at this ⊢; omega
      · unfold Apart; omega
    · have := hrg.g; rw [h28]; unfold Apart at this ⊢; simp only [grd] at this; omega
    · rw [h28]; unfold Apart at hga ⊢; omega
  refine ReachesRet.call_regions (svvD impl hap R bk Lk) hpc hpre fun T' hT hq hrgT => ?_
  obtain ⟨junk, f, v, fpsr, m, rfl, ⟨hval, hcar, hfr⟩, hinv, -⟩ := hq
  simp only [ez', en', ex', ey', e80] at hval hcar hfr
  rw [h28] at hinv
  have hregm : m.regions = X.mem.regions := hrgT
  have hcar1 : m.readLE (s.sp.toNat - 320) 8 ≤ 1 := by rw [hcar]; split <;> omega
  -- the buffer after the call
  obtain ⟨hz1, hb1⟩ := Asm.subVV_model X.mem m qv qv c.vp (c.vl / 2 - 1) _ hcar1 hval
  have hV : Asm.limbs X.mem c.vp (c.vl / 2 - 1) = (c.V s).take (c.vl / 2 - 1) := by
    rw [← Asm.limbs_take X.mem c.vp c.vl _ (by omega), limbs_congr hmc.bd.vk]
  have hB : Asm.limbs X.mem qv (c.vl / 2 - 1) = st.buf.take (c.vl / 2 - 1) := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hs3]
  have hbf : Asm.limbs m qv (3 * c.vl) = (stV (c.V s) (c.vl / 2 - 1) st).buf := by
    rw [Asm.limbs_upd (m := X.mem) (j := 0) (k := c.vl / 2 - 1) (by omega) (fun i hi hi2 => hfr.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)), Mdl.upd_zero, hmc.bf]
    simp only [Nat.mul_zero, Nat.add_zero, Asm.length_limbs]
    rw [hz1, hB, hV]
  -- the frame of the call in the `Mc.callN` form
  have hF' : MemFrame X.mem m (R.rt ++ winA X 0 88 ++ [(qv, qv + 8 * (c.vl / 2 - 1))]) := hfr.mono fun x n ho => by
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    rw [hspn] at ho; omega
  have hL' : LiveFrame X.mem m Lk [(qv, qv + 8 * (c.vl / 2 - 1))] := ⟨fun x n hin ho => hfr.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ho ⊢
    rw [hspn] at this; omega)⟩
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Outside x n [(qv, qv + 8 * (c.vl / 2 - 1))] →
      m.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hF' hL' hh hw' ho
  have hloc := hmc.qloc.out
  have hsub : ∀ x n, Outside x n [(qv, qv + 8 * (3 * c.vl))] → Outside x n [(qv, qv + 8 * (c.vl / 2 - 1))] :=
    fun x n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have ap : ∀ {x n}, Apart qv (8 * (3 * c.vl)) x n → Apart x n qv (8 * (c.vl / 2 - 1)) := fun h => by
    unfold Apart at h ⊢; omega
  have ht0 := hrg.t0
  have hu := hrg.u
  have kT : m.readLE c.t0 (8 * (c.q0 s j U).length) = X.mem.readLE c.t0 (8 * (c.q0 s j U).length) := by
    have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at ht0; simp only [outside_cons, outside_nil, and_true]; omega
  have kW : m.readLE (c.up + 8 * (j - c.vl / 2)) (8 * (c.u1 - (j - c.vl / 2))) =
      X.mem.readLE (c.up + 8 * (j - c.vl / 2)) (8 * (c.u1 - (j - c.vl / 2))) :=
    rk _ _ (hext.held (huh.sub (by omega) (by omega))) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hu; simp only [outside_cons, outside_nil, and_true]; omega)
  have hmcT : Mc R c s Lk bk m j Z U qv (stV (c.V s) (c.vl / 2 - 1) st) :=
    Mc.callN hmc hspn (by omega) (by omega) hF' hL' (LiveExt.refl R Lk) hinv hregm (Nat.le_refl _)
      (fun x n h => hsub _ _ (hloc.1 x n h)) (fun x n h1 h2 => hsub _ _ (hloc.2 x n h1 h2))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by have := hrg.st; unfold Apart at this ⊢; omega) (ap hrg.v)
      (ap (apSR hrg.u (by omega) (by omega))) (ap hrg.q) (ap (apSR hrg.u (Nat.le_refl _) (by omega)))
      (by rw [limbs_congr kT]; exact hmc.qk) hbf (by rw [limbs_congr kW]; exact hmc.wk)
  -- the slots
  have o : ∀ a, (a + 8 ≤ s.sp.toNat - 320 ∨ s.sp.toNat - 312 ≤ a) → s.sp.toNat - 408 ≤ a →
      a + 8 ≤ s.sp.toNat + 96 → m.readLE a 8 = X.mem.readLE a 8 := fun a h1 h2 h3 => hfr.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]; omega)
  have hv4 := hbx.v4
  refine k _ (by show X.regs 30 = _; exact h30) ⟨hsp, by rw [ret0_r _ _ _ _ _ _ 28 (by omega)]; exact h28,
    by rw [ret0_r _ _ _ _ _ _ 29 (by omega)]; exact h29, by rw [ret0_r _ _ _ _ _ _ 18 (by omega)]; exact h18, hmcT,
    ⟨?_, ?_, ?_⟩, ?_, hbx.hi, hbx.pos, hbx.inv⟩ ?_
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hv4.s328
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hv4.s152
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hv4.s168
  · show m.readLE _ _ = _
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hbx.si
  · show m.readLE _ _ = _
    rw [← hB, ← hV]; exact hb1

end FvModexp.Arm64.DivRec
