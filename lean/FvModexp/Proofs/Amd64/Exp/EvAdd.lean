import FvModexp.Proofs.Amd64.Exp.EvAddP
import FvModexp.Proofs.Amd64.Exp.EvTrR
import FvModexp.Proofs.Amd64.Exp.EvTr
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): **`segAdd`** — `J14` (`mul2R`) → `z = z.add(z, u)` → `J15` (`addR`) (asm s64; twin of
infra's arm64 `EvAdd`)

`runAdd` (EvTrR): `RAX/RBX/RCX ← 0x108/0xa0/0xa8` (`z`), `RDI/RSI/R8` the same, `R9..R11 ← RAX/RBX/RCX` (`u`),
`CALL nat.add` (ret `addR`). Premise `AddHypR0` (divmc's empty-tolerant `NatAdd.ensR0`), `addPre0`, a non-stack callee
(`frm_dstZ` + `stepC`). `J15`: the result `(p, l, c)` in the exit form — `NatOF` relative to the ENTRY `z` / live
set `L` (need `1`: a fresh result is non-empty), and `ResSep`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp

/-- the join point `addR` (return of `z.add(z, u)`): `RAX/RBX/RCX` = the function's result -/
structure J15 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 p l c : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 addR
  r0 : S.regs 0 = BitVec.ofNat 64 p
  r3 : S.regs 3 = BitVec.ofNat 64 l
  r1 : S.regs 1 = BitVec.ofNat 64 c
  res : ExpHyp.NatOF R L L1 S.mem zp zc 1 p l c (vZ2 s xp xl yp yl mp ml + vU s xp xl yp yl mp ml)
  rs : ResSep s.mem S.mem st p c
  p64 : p < 2 ^ 64

theorem norm_zeroE {m : Memory} {p l : Nat} (hv : natVal m p l = 0) (hn : NatNorm m p l) : l = 0 := by
  rcases hn with h | h
  · exact h
  rcases l with _ | l
  · rfl
  exfalso; apply h
  rw [Nat.add_sub_cancel]
  unfold natVal at hv
  rw [show 8 * (l + 1) = 8 * l + 8 by omega, Janus.Arm64.Memory.readLE_add] at hv
  have h2 : 256 ^ (8 * l) * m.readLE (p + 8 * l) 8 = 0 := by omega
  rcases Nat.mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by decide)))
  · exact h3

theorem natVal_zero_len (m : Memory) (p : Nat) : natVal m p 0 = 0 := by
  unfold natVal; simp [Janus.Arm64.Memory.readLE]

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

/-- the arithmetic of `segAdd` (outside the big context) -/
theorem addA {lw lu ml : Nat} (hml : ml ≤ 128) (hlw : lw ≤ ml) (hlu : lu ≤ ml) :
    (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ ml + 1 ∧ lw ≤ 2 ^ 12 ∧ lu ≤ 2 ^ 12 ∧
      max lw lu < 2 ^ 39 := by
  refine ⟨?_, by omega, by omega, by omega⟩
  split <;> omega

theorem pos_of_nle {a b : Nat} (h : ¬ a ≤ b) : 0 < a := by omega

theorem natAdd_subE : ∀ x, LibNatAdd.names.contains x = true → LibNE.names.contains x = true := by
  have h : LibNatAdd.names.Sublist LibNE.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem natAdd_nfE : LibNatAdd.names.contains fn = false := by decide +kernel

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J14` → `J15`** (see the module doc) -/
theorem segAdd {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) (hadd : AddHypR0 impl R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hzw : Outside zp (8 * zc) [(sp - 8 - K, sp + 0x1b8)])
    {rk rk' : Nat} (hrk : ∀ k, k ≤ ml + 1 → makeCost k + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K15 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 l2 p l c : Nat),
      J15 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 l1 l2 p l c →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 l2 lw pZ cZ pu lu cu : Nat}
    (h : J14 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 l1 l2 lw pZ cZ pu lu cu) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
  have hspl : sp < 2 ^ 64 := by omega
  have hK8 := addK hk
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hMl : natVal s.mem mp ml < 2 ^ (64 * ml) := natVal_lt64 _ _ _
  have hlw : lw ≤ ml := nlen_bd' h.zs.2.2.2.2.2
    (by rw [h.zs.2.2.2.2.1]; exact Nat.lt_trans (vZ2_lt s xp xl yp yl mp ml hM) hMl)
  have hlu : lu ≤ ml := nlen_bd' h.u.2.2.2
    (by rw [h.u.2.2.1]; exact Nat.lt_trans (vU_lt s xp xl yp yl mp ml hM) hMl)
  obtain ⟨hneed, hlw12, hlu12, hmx⟩ := addA hml hlw hlu
  have hrk' := hrk _ hneed
  have hcu := h.u.1.1
  have hcZ := h.zs.1
  have hlwc := h.zs.2.2.2.1
  have hluc := h.u.2.1
  refine runAdd ret0 Q sp pZ lw cZ S.mem hacc0 hsp8 (by omega) h.s108 h.sa0 h.sa8 S h.pc h.jx.esp rfl ?_
  intro S2 M2 f0 f4 fm hF hrg frd r0 r3 r1 r7 r6 r8 r9 r10 r11 r5 r14 rfs rx15 rdf
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (own1 sp K hsp8)
  have hhd : HdrEq st S.mem M2 := by
    have kF : ∀ a, (a + 8 ≤ sp - 8 ∨ sp ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 =>
      hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hstw := hP.stkF.1
    unfold Apart at hstw
    refine ⟨?_, kF _ (by omega), kF _ (by omega)⟩
    have := kF (st + 0) (by omega); simpa using this
  have hu0 := hown _ _ _ _ h.u
  have hzs := LZ.frm hP hw (LiveExt.refl R L1) hF.accessible hhd (d := 0) (n := 0)
    (fun a k _ hw0 _ => hF.readLE a k (by
      unfold Apart at hw0; simp only [outside_cons, outside_nil, and_true]; omega)) h.zs
    (fun _ => by unfold Apart; omega)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  have hpre := addPre0 hP hw2 hzw tsp tg tfs fm hzs h.Ze h.pZ64 hu0 h.pu64 h.uz hlw12 hlu12 (bud_pre hb1 hrk')
  have hS := Ensures.toSummaryIn (hadd b1 L1 (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 lw) (BitVec.ofNat 64 cZ)
    (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 lw) (BitVec.ofNat 64 cZ) (BitVec.ofNat 64 pu) (BitVec.ofNat 64 lu)
    (BitVec.ofNat 64 cu))
    (A64.noExit_restrict64 hap LibNatAdd.names) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap natAdd_subE)
  rw [add_aE] at hS
  have t1 := tA h.pZ64
  have t2 := tA (lt64 (lt40 hlwc hcZ))
  have t3 := tA (lt64 hcZ)
  have t4 := tA h.pu64
  have t5 := tA (lt64 (lt40 hluc hcu))
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, hpre⟩
    (fun s' hr hq hrg' => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap natAdd_nfE 1353 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0, r3, r1, r7, r6, r8, r9.trans h.r0, r10.trans h.r3, r11.trans h.r1, trivial⟩
  obtain ⟨⟨e4, -, e14, ex15⟩, hq, hreu, hc40⟩ := hq
  simp only [NatAdd.Post, NatAdd.PostS, NatAdd.need, NatAdd.mx, t1, t2, t3, t4, t5] at hq hreu hc40
  obtain ⟨efs, edf, p', n', c', g0, g1, g2, hv, hN, hlc, -, L2, b2, hx, hb, hinv, hlv, hor, hF', hLF'⟩ := hq
  simp only [win, tsp] at hF'
  rw [fm] at hF' hLF' hrg' hv
  rw [hzs.2.2.2.2.1, hu0.2.2.1] at hv
  rw [tg] at hinv
  have hc' : c' < 2 ^ 40 := by rw [← g2]; exact hc40 hmx
  obtain ⟨qd, kd, hds, hdl, hdw, hF'', hLF'', hsb, ehd⟩ :=
    frm_dstZ hP hw2 hzs hx (stk := 4440) (above := 80) hK8.1 (by decide) hF' hLF'
  obtain ⟨hw', hkc, -⟩ := stepC hP hw2 hds hdl hdw (stk := 4440) (above := 80) hK8.1 (by decide) hF'' hLF''
    hrg' hx hinv hsb
  have hk' := kk_push1 hsp8 (by decide) hF hkc
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, f4]; exact bv_add8 hsp8 hspl
  have hjx := h.jx.call (hS4.trans h.jx.esp.symm) (e14.trans r14) (by rw [efs, rfs]) (ex15.trans rx15)
    (edf.trans rdf) hw' hk' (bud_step hb1 hrk' hb)
  have hp' : p' < 2 ^ 64 := by rw [← g0]; exact BitVec.isLt _
  -- the result relative to the entry
  have hreuse : p' = pZ ∧ c' = cZ → ExpHyp.NatOF R L L2 s'.mem zp zc 1 p' n' c' (vZ2 s xp xl yp yl mp ml +
      vU s xp xl yp yl mp ml) ∧ ResSep s.mem s'.mem st p' c' := by
    rintro ⟨rfl, rfl⟩
    refine ⟨⟨hv, hN, hlc, hc', hlv, ?_⟩, fun hc hn => ?_⟩
    · rcases Nat.eq_zero_or_pos c' with c0 | c0
      · exact Or.inl (h.Ze c0)
      · rcases hzs.2.2.1 c0 with e | ⟨hin, hap, -⟩
        · exact Or.inl e
        · exact Or.inr ⟨c0, hin, hap⟩
    · rcases hzs.2.2.1 hc with ⟨rfl, rfl⟩ | ⟨-, -, hob⟩
      · exact rs_zE hP hw' hc hn
      · exact (hob.back hx hsb.1).2
  have hfresh' : InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1 → ¬ ((if min lw lu = 0 then max lw lu else
      max lw lu + 1) ≤ cZ) → ExpHyp.NatOF R L L2 s'.mem zp zc 1 p' n' c' (vZ2 s xp xl yp yl mp ml +
      vU s xp xl yp yl mp ml) ∧ ResSep s.mem s'.mem st p' c' := by
    rintro ⟨hin, hap⟩ hnd
    have h1 : 1 ≤ c' := add_pos hzs.2.2.2.2.2 hu0.2.2.2 (by rw [hv, hzs.2.2.2.2.1, hu0.2.2.1]) hlc
      (pos_of_nle hnd)
    refine ⟨⟨hv, hN, hlc, hc', hlv, Or.inr ⟨h1, hin, fun r hr => hap r (hw.le.mem_old hr)⟩⟩, fun hc hn => ?_⟩
    rw [ehd.1, ehd.2] at hn ⊢
    have := hap _ (hw2.ain hn).1
    simp only at this
    rwa [show stW M2 st + 8 * stCap M2 st - stW M2 st = 8 * stCap M2 st by omega] at this
  have hfin : ExpHyp.NatOF R L L2 s'.mem zp zc 1 p' n' c' (vZ2 s xp xl yp yl mp ml + vU s xp xl yp yl mp ml) ∧
      ResSep s.mem s'.mem st p' c' := by
    by_cases hnd : (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ cZ
    · obtain ⟨q0, q2⟩ := hreu hnd
      exact hreuse ⟨by rw [← g0, q0], by rw [← g2, q2]⟩
    · rcases hor with e | e
      · exact hreuse e
      · exact hfresh' e hnd
  exact K15 s' L2 b2 l1 l2 p' n' c' ⟨hjx, by rw [hr, retAddrOf_eq, tsp, fm, frd],
    BitVec.eq_of_toNat_eq (by rw [g0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp']),
    BitVec.eq_of_toNat_eq (by rw [g1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
    BitVec.eq_of_toNat_eq (by rw [g2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt64 hc')]),
    hfin.1, hfin.2, hp'⟩

end

end FvModexp.Amd64.ExpEven
