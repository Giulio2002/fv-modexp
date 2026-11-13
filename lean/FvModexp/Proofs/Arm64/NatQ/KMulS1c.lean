import FvModexp.Proofs.Arm64.NatQ.KMulB

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/KMulS1c.lean — TIGHT COSTS, divmc s34] `karatsuba` (arm64): `z1.mul(stk, tx, ty); clear(z)` (natmul.go:210-212), `KM2b → KM3`: the clear

`kS1clr`: from `0x1bc140` (the product returned) the `memclrNoHeapPointers(zp, 16n)` call (live contract) to `KM3`;
`kS1`: from `KM2b` to the inner `(*Int).mul` (`kn_icallR`: result in `t`, reused) and on to `kS1clr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le)
open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

theorem ksp_sub' (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the facts after `clear(z)` (`memclrNoHeapPointers`'s post, memory `w`) give `KM3` -/
theorem kS1post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {S : State} {w : Memory}
    (hkm : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc3 n) S.mem)
    {ng l1 : Nat} (hz1 : IntAt S.mem (s.sp.toNat - 264) ng t l1 (kT n)) (hng : ng ≤ 1) (hcan : ng = 1 → 0 < l1)
    (hl1 : l1 ≤ 2 * kh n)
    (hz1v : sgnV ng (natVal S.mem t l1) =
      ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int)))
    (hz1n : NatNorm S.mem t l1) (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hFc : MemFrame S.mem w (R.rt ++ [(s.sp.toNat - 448 - 4096, s.sp.toNat - 448 - 8),
      (s.sp.toNat - 448 + 8, s.sp.toNat - 448 + 8 + 16)] ++ [(zp, zp + 8 * (2 * n))]))
    (hLFc : LiveFrame S.mem w Lk [(zp, zp + 8 * (2 * n))])
    (hinvw : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk w)) (hz : Mem.Zeroed w zp (8 * (2 * n)))
    (hreg : w.regions = S.mem.regions) (S' : State) (hpos : KNAt s S' 0x1bc150) (hm : S'.mem = w) :
    KM3 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk bk ng l1 := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, -, -, -, -, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  have htops := hkm.tops
  have hstw : Outside st 24 (win s W 72) := hkm.F.stk.2.2.1
  have hsz : Apart st 24 zp (8 * zc) := hkm.F.zs.1
  have hzw : zp + 8 * zc ≤ s.sp.toNat - W ∨ s.sp.toNat + 72 ≤ zp := by
    have := hkm.F.zw; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  obtain ⟨hlive, htw, -, htz, -, -, ht48⟩ := htops
  simp only [win, outside_cons, outside_nil, and_true] at htw hstw
  unfold Apart at htz hsz
  have hF1 : MemFrame S.mem w (R.rt ++ [(s.sp.toNat - 448 - 4096, s.sp.toNat - 448 - 8),
      (s.sp.toNat - 448 + 8, s.sp.toNat - 448 + 24)] ++ [(zp, zp + 8 * (2 * n))]) :=
    hFc.mono fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, ho.1.2.1, by omega⟩, ho.2⟩
  have hsbC : StackBackL R Lk Lk st S.mem w ∧ stCap w st = stCap S.mem st := by
    refine NatSqr.stackBack_keepC hkm.sok (ws := [(s.sp.toNat - 448 - 4096, s.sp.toNat - 448 - 8),
      (s.sp.toNat - 448 + 8, s.sp.toNat - 448 + 8 + 16)] ++ [(zp, zp + 8 * (2 * n))]) ?_
      (FvModexp.LiveFrame.mono_ws hLFc fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ (LiveExt.refl R Lk)
    · rw [← List.append_assoc]; exact hFc
    · simp only [outside_append, outside_cons, outside_nil, and_true]; omega
  have hkm1 := hkm.step (k := 4096) (a := 24) (by omega) (by omega) (ws := [(zp, zp + 8 * (2 * n))])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩)
    hF1 hLFc hreg (LiveExt.refl R Lk) (c := 0) (Or.inr ⟨by omega, hsbC.2⟩) (by have := hkm.spk; omega) hinvw hsbC.1
  rw [Nat.add_zero] at hkm1
  have hrd : ∀ x m, s.sp.toNat - 368 ≤ x → x + m ≤ s.sp.toNat + 72 → w.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 => hkm.rdW (k := 4096) (a := 24) (by omega) (by omega) hF1 h1 h2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have htH : Held R Lk t (8 * kT n) := hkm.scr.held
  have hrt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → w.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 => Held.readLE2 (htH.sub h1 h2) hFc hLFc
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hkh : kh n = (n + 1) / 2 := rfl
  have htv : natVal w t l1 = natVal S.mem t l1 := by
    unfold natVal; exact hrt _ _ (Nat.le_refl _) (by simp only [kT]; omega)
  subst hm
  refine ⟨hpos, hkm1, NatSqr.IntAt.keep hz1 fun x m h1 h2 => hrd x m (by omega) (by omega), hng, hcan, hl1, ?_, ?_,
    NatSqr.IntAt.keep hz0 fun x m h1 h2 => hrd x m (by omega) (by omega),
    NatSqr.IntAt.keep hz2 fun x m h1 h2 => hrd x m (by omega) (by omega), ?_⟩
  · rw [htv]; exact hz1v
  · rcases hz1n with h0 | h0
    · exact Or.inl h0
    · by_cases hl0 : l1 = 0
      · exact Or.inl hl0
      · right; rwa [hrt _ _ (by omega) (by simp only [kT]; omega)]
  · unfold natVal; exact FvModexp.readLE_of_zeroed hz _ _ (Nat.le_refl _) (Nat.le_refl _)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem kS1clr (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bc140)
    (hsp : S.sp = s.sp - 448#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 456#64)
    (h18 : S.regs 18 = s.regs 18)
    (hkm : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc3 n) S.mem)
    {ng l1 : Nat} (hz1 : IntAt S.mem (s.sp.toNat - 264) ng t l1 (kT n)) (hng : ng ≤ 1) (hcan : ng = 1 → 0 < l1)
    (hl1 : l1 ≤ 2 * kh n)
    (hz1v : sgnV ng (natVal S.mem t l1) =
      ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int)))
    (hz1n : NatNorm S.mem t l1)
    (hz0 : Z0H s S.mem zp zc n) (hz2 : Z2H s S.mem zp zc n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' ng l1 : Nat),
      KM3 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibMul.names
  have hmc' := MemclrNoHeapPointersLive.of_codeIn hc hmc
  clear hc
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, -, -, -, -, hzl, hzc40, hout, hgr, hga⟩ := hkm.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, hzal, hzh, hz48⟩ := hkm.zops
  have F := hkm.F
  have hsv : RunIface.Serves R := F.sv
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [zp, 8 * (2 * n)] := hsv.2.2.1 _ _ (by omega)
  have hzacc : S.mem.accessible zp (8 * (2 * n)) true = true := by
    obtain ⟨-, -, hacc, -⟩ := hzlive (by omega); exact Memory.accessible_mono _ hacc (by omega) (by omega)
  have hzH : InRanges zp (8 * (2 * n)) Lk ∨ Outside zp (8 * (2 * n)) R.rt := hzh.sub (by omega) (by omega)
  have hzg' : Apart zp (8 * (2 * n)) ((s.regs 28).toNat + 16) 8 := by
    simp only [NatSqr.guard] at hzg; unfold Apart at hzg ⊢; omega
  have hzw' : zp + 8 * (2 * n) ≤ s.sp.toNat - W ∨ s.sp.toNat + 72 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  have hgQ := hkm.grd
  obtain ⟨⟨hg1, hg2, hg3⟩, -⟩ := F.env
  have hg2' : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hkm.fr.accessible]; exact hg2
  have hg3' : S.mem.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 448 := by rw [hgQ]; omega
  have hga1 : (s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 448 - 4096 ∨
      s.sp.toNat - 448 - 8 ≤ (s.regs 28).toNat + 16 := by
    unfold Apart at hga; omega
  have hga2 : (s.regs 28).toNat + 16 ≤ s.sp.toNat - 448 ∨ s.sp.toNat - 448 + 8 ≤ (s.regs 28).toNat := by
    unfold Apart at hga; omega
  clear hg2 hg3
  have hL1 := hkm.lsep
  have hinv := hkm.inv
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 72) true = true := F.env.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - W) (W + 72) true = true := by rw [hkm.fr.accessible]; exact hw0
  clear hw0
  have q344 : S.mem.readLE (s.sp.toNat + 24) 8 = 2 * n := hkm.s3
  have q336 : S.mem.readLE (s.sp.toNat + 16) 8 = zp := hkm.s2
  unfold KNGoal
  clear F hzlive hzw hzg hzh hsv hgQ hga hgr
  janus_run [q344, q336] until [0x1bc150] calls [hmc' Lk bk]
  rename_i jk fl vv w ex ep hFc hLFc hinvw hz
  have hreg : w.regions = S.mem.regions := by janus_assumption
  refine hK _ Lk bk ng l1 (kS1post hkm hz1 hng hcan hl1 hz1v hz1n hz0 hz2 hFc hLFc hinvw hz hreg _
    ⟨rfl, rfl, ?_, ?_, ?_⟩ rfl)
  · simp only [retStateX, callRegs_apply]; simp; exact h28
  · simp only [retStateX, callRegs_apply]; simp; exact h29
  · simp only [retStateX, callRegs_apply]; simp; exact h18

end FvModexp.Arm64.Q.NatMul
