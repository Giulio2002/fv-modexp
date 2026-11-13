import FvModexp.Proofs.Arm64.Exp.EvAddP

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): **`segAdd`** — `J14` (`mul2R`) → `z = z.add(z, u)` → `J15` (`addR`) (agent infra)

`runAdd`: `R3..R5 ← 272/168/176` (`z`), `R6..R8 ← R0..R2` (`u`), `R0..R2 ← R3..R5`, `CALL nat.add` (ret `addR`).
Premise `AddHypR0` (divmc's empty-tolerant `NatAdd.ensR0` is an instance), `addPre0`, a non-stack callee
(`frm_dstZ` + `stepC0`). `J15`: the result `(p, l, c)` in the exit form — `NatOF` relative to the ENTRY `z` / live
set `L` (need `1`: a fresh result is non-empty, since `need ≤ cZ` reuses `z` and `need > 0` makes the value
positive), and `ResSep` (the result is apart from the stack's array when that is not the entry one).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the join point `addR` (return of `z.add(z, u)`): `X0..X2` = the function's result -/
structure J15 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 p l c : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 addR
  r0 : S.regs 0 = BitVec.ofNat 64 p
  r1 : S.regs 1 = BitVec.ofNat 64 l
  r2 : S.regs 2 = BitVec.ofNat 64 c
  res : ExpHyp.NatOF R L L1 S.mem zp zc 1 p l c (vZ2 s xp xl yp yl mp ml + vU s xp xl yp yl mp ml)
  rs : ResSep s.mem S.mem st p c
  p64 : p < 2 ^ 64

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mul2R` → `nat.add`'s entry -/
theorem runAdd {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp pZ lw cZ : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 false = true)
    (h272 : M.readLE (sp + 272) 8 = pZ) (h168 : M.readLE (sp + 168) 8 = lw) (h176 : M.readLE (sp + 176) 8 = cZ)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mul2R) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1781184 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pZ → S'.regs 1 = BitVec.ofNat 64 lw → S'.regs 2 = BitVec.ofNat 64 cZ →
      S'.regs 3 = BitVec.ofNat 64 pZ → S'.regs 4 = BitVec.ofNat 64 lw → S'.regs 5 = BitVec.ofNat 64 cZ →
      S'.regs 6 = S.regs 0 → S'.regs 7 = S.regs 1 → S'.regs 8 = S.regs 2 →
      S'.regs 30 = BitVec.ofNat 64 addR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at KN
  generalize e1 : S.regs 1 = x1 at KN
  generalize e2 : S.regs 2 = x2 at KN
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  janus_run [h272, h168, h176, hacc, hal] until [1781184]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

theorem norm_zeroE {m : Memory} {p l : Nat} (hv : natVal m p l = 0) (hn : NatNorm m p l) : l = 0 := by
  rcases hn with h | h
  · exact h
  rcases l with _ | l
  · rfl
  exfalso; apply h
  rw [Nat.add_sub_cancel]
  unfold natVal at hv
  rw [show 8 * (l + 1) = 8 * l + 8 by omega, Memory.readLE_add] at hv
  have h2 : 256 ^ (8 * l) * m.readLE (p + 8 * l) 8 = 0 := by omega
  rcases Nat.mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by decide)))
  · exact h3

theorem natVal_lt64E (m : Memory) (p l : Nat) : natVal m p l < 2 ^ (64 * l) := by
  have := Memory.readLE_lt m p (8 * l)
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * l) = 64 * l by omega] at this
  exact this

theorem natVal_zero_len (m : Memory) (p : Nat) : natVal m p 0 = 0 := by
  unfold natVal; simp [Memory.readLE]

/-- the value bound of `u` -/
theorem vU_lt (s : State) (xp xl yp yl mp ml : Nat) (hM : 0 < natVal s.mem mp ml) :
    vU s xp xl yp yl mp ml < natVal s.mem mp ml := by
  simp only [vU]
  have hq : 0 < natVal s.mem mp ml / 2 ^ nE s mp ml := by
    have := (Exp.tz_spec hM).2
    rcases Nat.eq_zero_or_pos (natVal s.mem mp ml / 2 ^ nE s mp ml) with e | e
    · rw [e] at this; exact absurd this (by decide)
    · exact e
  have h1 := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt (vT s xp xl yp yl mp ml) (Nat.two_pow_pos (nE s mp ml))) hq
  have h2 := Nat.mul_div_le (natVal s.mem mp ml) (2 ^ nE s mp ml)
  have h3 := Nat.mul_comm (2 ^ nE s mp ml) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  omega

theorem vZ2_lt (s : State) (xp xl yp yl mp ml : Nat) (hM : 0 < natVal s.mem mp ml) :
    vZ2 s xp xl yp yl mp ml < natVal s.mem mp ml := by
  simp only [vZ2]
  have hq : 0 < natVal s.mem mp ml / 2 ^ nE s mp ml := by
    have := (Exp.tz_spec hM).2
    rcases Nat.eq_zero_or_pos (natVal s.mem mp ml / 2 ^ nE s mp ml) with e | e
    · rw [e] at this; exact absurd this (by decide)
    · exact e
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hq) (Nat.div_le_self _ _)

/-- a fresh `add` result is non-empty: otherwise `need = 0 ≤ cZ` (the reuse case) -/
theorem add_pos {m m' : Memory} {pZ lw pu lu p' n' c' : Nat} (hnz : NatNorm m pZ lw) (hnu : NatNorm m pu lu)
    (hv : natVal m' p' n' = natVal m pZ lw + natVal m pu lu) (hnc : n' ≤ c')
    (hneed : 0 < (if min lw lu = 0 then max lw lu else max lw lu + 1)) : 1 ≤ c' := by
  rcases Nat.eq_zero_or_pos n' with e | e
  · subst e
    rw [natVal_zero_len] at hv
    have h1 : natVal m pZ lw = 0 := by omega
    have h2 : natVal m pu lu = 0 := by omega
    have := norm_zeroE h1 hnz
    have := norm_zeroE h2 hnu
    subst_vars
    simp at hneed
  · omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

theorem natAdd_sub : ∀ x, NatAdd.names.contains x = true → LibNE.names.contains x = true :=
  fun x hx => libW_sub x (SubMod2N.add_names x hx)

theorem natAdd_nf : NatAdd.names.contains fn = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J14` → `J15`** (see the module doc) -/
theorem segAdd {impl : List Segment} (hap : ImplApart Extracted.program impl) (hadd : AddHypR0 impl R)
    (hK4 : 4464 ≤ K) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hzw : Outside zp (8 * zc) [(sp - K, sp + 448)])
    {rk rk' : Nat} (hrk : ∀ k, k ≤ ml + 1 → makeCost k + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K15 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 p l c : Nat),
      J15 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 l1 l2 p l c →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 l2 lw pZ cZ pu lu cu : Nat}
    (h : J14 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 l1 l2 lw pZ cZ pu lu cu) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hKs := hP.1.2.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hgN : (S.regs 28).toNat = g := by rw [h.jx.e28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hacc : S.mem.accessible (sp + 128) 320 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  have hMl : natVal s.mem mp ml < 2 ^ (64 * ml) := natVal_lt64E _ _ _
  have hlw : lw ≤ ml := nlen_bd' h.zs.2.2.2.2.2 (by rw [h.zs.2.2.2.2.1]; exact Nat.lt_trans (vZ2_lt s xp xl yp yl mp ml hM) hMl)
  have hlu : lu ≤ ml := nlen_bd' h.u.2.2.2 (by rw [h.u.2.2.1]; exact Nat.lt_trans (vU_lt s xp xl yp yl mp ml hM) hMl)
  have hneed : (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ ml + 1 := by split <;> omega
  have hcu := h.u.1.1
  have hcZ := h.zs.1
  refine runAdd ret0 Q sp pZ lw cZ S.mem hal hsp2 hacc h.s272 h.s168 h.s176 S h.pc h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r7 r8 r30 r18 r28 r29
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  have hpre := addPre0 hP hw hK4 hzw (fsp.trans h.jx.esp) (r28.trans h.jx.e28) fm h.zs h.Ze h.pZ64 h.u h.pu64
    h.uz (by omega) (by omega) (bud_pre hb1 (hrk _ hneed))
  have hS := CallNE.hypSum hap natAdd_sub (hadd b1 L1 (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 lw) (BitVec.ofNat 64 cZ)
    (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 lw) (BitVec.ofNat 64 cZ) (BitVec.ofNat 64 pu) (BitVec.ofNat 64 lu)
    (BitVec.ofNat 64 cu))
  have t1 := LibCalls.tN h.pZ64
  have t2 := LibCalls.tN (show lw < 2 ^ 64 by omega)
  have t3 := LibCalls.tN (show cZ < 2 ^ 64 by omega)
  have t4 := LibCalls.tN h.pu64
  have t5 := LibCalls.tN (show lu < 2 ^ 64 by omega)
  have t6 := LibCalls.tN (show cu < 2 ^ 64 by omega)
  refine ReachesRet.call_regions hS (by rw [f0, show segAddr Extracted.program NatAdd.fn = 1781184 by decide])
    ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hreu, hc40⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [addR]; omega)]
    exact ra_ev hap natAdd_nf 214 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0, r1, r2, r3, r4, r5, r6.trans h.r0, r7.trans h.r1, r8.trans h.r2, trivial⟩
  · simp only [NatAdd.Post, NatAdd.PostS, NatAdd.need, NatAdd.mx, t1, t2, t3, t4, t5] at hq hreu hc40
    obtain ⟨p', n', c', g0, g1, g2, hv, hN, hlc, -, L2, b2, hx, hb, hinv, hlv, hor, hF, hLF⟩ := hq
    simp only [winA, hsN'] at hF
    rw [fm] at hF hLF hrg hv
    rw [h.zs.2.2.2.2.1, h.u.2.2.1] at hv
    rw [r28, h.jx.e28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hP.1.2.2.1; omega)] at hinv
    have hc' : c' < 2 ^ 40 := by rw [← g2]; exact hc40 (by omega)
    obtain ⟨qd, kd, hds, hdl, hdw, hF', hLF', hsb, ehd⟩ :=
      frm_dstZ hP hw h.zs hx (stk := 4464) (above := 80) hK4 (by omega) hF hLF
    obtain ⟨hw', hk, -⟩ := stepC0 hP hw hds hdl hdw (stk := 4464) (above := 80) hK4 (by omega) hF' hLF' hrg
      hx hinv hsb
    have hjx := h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw' hk (by omega)
      (bud_step hb1 (hrk _ hneed) hb)
    have hp' : p' < 2 ^ 64 := by rw [← g0]; exact BitVec.isLt _
    -- the result relative to the entry
    have hreuse : p' = pZ ∧ c' = cZ → ExpHyp.NatOF R L L2 s'.mem zp zc 1 p' n' c' (vZ2 s xp xl yp yl mp ml +
        vU s xp xl yp yl mp ml) ∧ ResSep s.mem s'.mem st p' c' := by
      rintro ⟨rfl, rfl⟩
      refine ⟨⟨hv, hN, hlc, hc', hlv, ?_⟩, fun hc hn => ?_⟩
      · rcases Nat.eq_zero_or_pos c' with c0 | c0
        · exact Or.inl (h.Ze c0)
        · rcases h.zs.2.2.1 c0 with e | ⟨hin, hap, -⟩
          · exact Or.inl e
          · exact Or.inr ⟨c0, hin, hap⟩
      · rcases h.zs.2.2.1 hc with ⟨rfl, rfl⟩ | ⟨-, -, hob⟩
        · exact rs_zE hP hw' hc hn
        · exact (hob.back hx hsb.1).2
    have hfresh' : InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1 → ¬ ((if min lw lu = 0 then max lw lu else
        max lw lu + 1) ≤ cZ) → ExpHyp.NatOF R L L2 s'.mem zp zc 1 p' n' c' (vZ2 s xp xl yp yl mp ml +
        vU s xp xl yp yl mp ml) ∧ ResSep s.mem s'.mem st p' c' := by
      rintro ⟨hin, hap⟩ hnd
      have h1 : 1 ≤ c' := add_pos h.zs.2.2.2.2.2 h.u.2.2.2 (by rw [hv, h.zs.2.2.2.2.1, h.u.2.2.1]) hlc (by omega)
      refine ⟨⟨hv, hN, hlc, hc', hlv, Or.inr ⟨h1, hin, SubMod2N.fresh_of hw.le hap⟩⟩, fun hc hn => ?_⟩
      rw [ehd.1, ehd.2] at hn ⊢
      have := hap _ (hw.ain hn).1
      simp only at this
      rwa [show stW S.mem st + 8 * stCap S.mem st - stW S.mem st = 8 * stCap S.mem st by omega] at this
    have hfin : ExpHyp.NatOF R L L2 s'.mem zp zc 1 p' n' c' (vZ2 s xp xl yp yl mp ml + vU s xp xl yp yl mp ml) ∧
        ResSep s.mem s'.mem st p' c' := by
      by_cases hnd : (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ cZ
      · obtain ⟨q0, q2⟩ := hreu hnd
        exact hreuse ⟨by rw [← g0, q0], by rw [← g2, q2]⟩
      · rcases hor with e | e
        · exact hreuse e
        · exact hfresh' e hnd
    exact K15 s' L2 b2 l1 l2 p' n' c' ⟨hjx, hr.trans r30,
      BitVec.eq_of_toNat_eq (by rw [g0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp']),
      BitVec.eq_of_toNat_eq (by rw [g1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
      BitVec.eq_of_toNat_eq (by rw [g2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
      hfin.1, hfin.2, hp'⟩

end

end FvModexp.Arm64.ExpEven
