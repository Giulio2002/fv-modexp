import FvModexp.Proofs.Arm64.Nat.KMulI
import FvModexp.Proofs.Arm64.Nat.KMulS1c

set_option autoImplicit false

/-!
# `karatsuba` (arm64): `z1.mul(stk, tx, ty); clear(z)` (natmul.go:210-212), `KM2b → KM3`

`kS1clr`: from `0x1bc140` (the product returned) the `memclrNoHeapPointers(zp, 16n)` call (live contract) to `KM3`;
`kS1`: from `KM2b` to the inner `(*Int).mul` (`kn_icallR`: result in `t`, reused) and on to `kS1clr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le)
open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- the operand part of `Ops` for `z[o:o+l]` with the capacity to `z`'s end -/
theorem KN.zopX (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {o l : Nat}
    (hol : o + l ≤ 2 * n) (hl : l ≤ 2 ^ 12) :
    l ≤ zc - o ∧ zc - o < 2 ^ 40 ∧ l ≤ 2 ^ 12 ∧ M.accessible (zp + 8 * o) (8 * l) false = true ∧
      (0 < zc - o → Held R Lk (zp + 8 * o) (8 * (zc - o)) ∧ zp + 8 * o + 8 * (zc - o) ≤ 2 ^ 48) ∧
      (0 < l → Outside (zp + 8 * o) (8 * l) (win s W 72) ∧ StkSep M st (zp + 8 * o) (8 * l)) := by
  obtain ⟨hacc, -, hH, h48, hw, hs, -⟩ := h.partZ hol
  have hzl := h.F.zc2
  have hzc := h.F.zc40
  exact ⟨by omega, by omega, hl, hacc, fun _ => ⟨hH, h48⟩, fun _ => ⟨hw, hs⟩⟩

end

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`KM2b → KM3`**: `z1.mul(stk, tx, ty)` (`0x1bc12c … 0x1bc13c`, `kn_icallR`), then `kS1clr` -/
theorem kS1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    (ih : ∀ j, IH impl R (8 * n + 2) j)
    {Lk : List (Nat × Nat)} {bk tng ltx yng lty : Nat} (S : State)
    (hB : KM2b R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk tng ltx yng lty)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' ng l1 : Nat),
      KM3 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' ng l1 →
      KNGoal impl R b L W st zp xp n yp s S') :
    KNGoal impl R b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have hkh : kh n = (n + 1) / 2 := rfl
  have hltx := hB.hltx; have hlty := hB.hlty
  obtain ⟨t1, t2, t3, t4⟩ := hB.txh
  obtain ⟨y1, y2, y3, y4⟩ := hB.tyh
  obtain ⟨z1, z2, z3, z4⟩ := hB.z1h
  obtain ⟨hlive, htw, htg, htz, -, -, ht48⟩ := hkm.tops
  have hts := hkm.tsep
  have hxo := hkm.zopX (o := 0) (l := ltx) (by omega) (by omega)
  have hyo := hkm.zopX (o := kh n) (l := lty) (by omega) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hxo
  have hsl : stLen S.mem st + 4 * (ltx + lty) + 64 ≤ 2 ^ 16 := by
    rw [hkm.slen]; have := hkm.F.slb; simp only [StackNat.rnd, kT]; omega
  have hops : Ops R Lk S.mem (s.regs 28).toNat (win s W 72) st (hP S.mem (s.sp.toNat - 264))
      (hC S.mem (s.sp.toNat - 264)) (hP S.mem (s.sp.toNat - 296)) (hL S.mem (s.sp.toNat - 296))
      (hC S.mem (s.sp.toNat - 296)) (hP S.mem (s.sp.toNat - 328)) (hL S.mem (s.sp.toNat - 328))
      (hC S.mem (s.sp.toNat - 328)) := by
    simp only [hP, hL, hC, t2, t3, t4, y2, y3, y4, z2, z4]
    refine ⟨hxo, hyo, ⟨by simp only [kT]; omega, hlive, htw, fun _ => ⟨htg, hts⟩, Or.inr fun _ _ => ?_,
      Or.inr fun _ _ => ?_⟩, hsl⟩
    · unfold Apart at htz ⊢; omega
    · unfold Apart at htz ⊢; omega
  have q456 : S.mem.readLE (s.sp.toNat + 8) 8 = st := hkm.s1
  have hsacc : S.mem.accessible (s.sp.toNat - 456) 528 false = true := by
    rw [hkm.fr.accessible]
    exact Memory.accessible_sub _ hkm.F.env.2.1.2.2.2 (Or.inr rfl) (by omega) (by omega)
  have hopsB := IntAS.Box.mk hops
  clear hops hxo hyo hlive htg hts hsl
  unfold KNGoal
  janus_run [q456] until [0x1b0c50]
  refine kn_icallR impl R hkm ih _ (by rfl) ?sp ?g ?hm ?l4 ?l48 ?r0 ?r1 ?r2 ?r3
    (Or.inl ⟨by omega, by omega⟩) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold Apart; omega) (by unfold Apart; omega) ?nx ?ny hopsB.h ?lx ?ly ?ru ?ne1 ?ne2 ?hq ?hsc ?K
  case hm => rfl
  case sp => simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  case g => janus_simp
  case l4 => janus_simp
  case l48 => janus_simp
  case r0 => janus_simp; exact ksp_sub' _ (by omega)
  case r1 => janus_simp
  case r2 => janus_simp; exact ksp_sub' _ (by omega)
  case r3 => janus_simp; exact ksp_sub' _ (by omega)
  case nx => simp only [hNeg, t1]; exact hB.htng
  case ny => simp only [hNeg, y1]; exact hB.hyng
  case lx => simp only [hL, t3]; exact hltx
  case ly => simp only [hL, y3]; exact hlty
  case ru => simp only [hL, hC, t3, y3, z4, kT]; omega
  case ne1 => simp only [hP, hC, z2, z4, t2, t4, kT]; unfold Apart at htz; simp only [kT] at htz; omega
  case ne2 => simp only [hP, hC, z2, z4, y2, y4, kT]; unfold Apart at htz; simp only [kT] at htz; omega
  case hq => simp only [hP, hL, z2, t3, y3, kT]; right; omega
  case hsc => have := kc7_le (stLen s.mem st) n; unfold kc7 kc6 kc5 kc4 kc3 at this; omega
  case K =>
    intro s2 Lk' bk' ng l' hr hreg hk hkm2 hz hng hcan hval hnn hl2 _ hF hLF
    have hspN : (s.sp - 448#64).toNat = s.sp.toNat - 448 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [hP, hC, hL, z2, z4, t3, y3] at hz hval hnn hl2 hF hLF
    have hix : intZ S.mem (s.sp.toNat - 296) = (kX0 s xp n : Int) - (kX1 s xp n : Int) := by
      rw [← hB.tv]; simp only [intZ, hNeg, hP, hL, t1, t2, t3, sgnV]
    have hiy : intZ S.mem (s.sp.toNat - 328) = (kX1 s yp n : Int) - (kX0 s yp n : Int) := by
      rw [← hB.yv]; simp only [intZ, hNeg, hP, hL, y1, y2, y3, sgnV]
    rw [hix, hiy] at hval
    simp only [winA, hspN] at hF
    rw [List.append_assoc] at hF
    have hzw := hkm.F.zw
    have hstw : Outside st 24 (win s W 72) := hkm.F.stk.2.2.1
    have hfrw := hkm.stk.2.2.1
    simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hzw hstw hfrw htw
    have hslc := hkm.sok.2.2.2.2.2.1
    have hkTd : kT n = 2 * kh n + 1 := rfl
    have hrd : ∀ x m, s.sp.toNat - 368 ≤ x → x + m ≤ s.sp.toNat + 72 → (x + m ≤ s.sp.toNat - 264 ∨
        s.sp.toNat - 232 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m :=
      fun x m h1 h2 h3 => hkm.rdW (k := W - 448) (a := 40) (by omega) (by omega) hF h1 h2
        (by simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
    refine kS1clr impl hap R hmc s2 (by rw [hr]; rfl) (by rw [hk.1]) (by rw [hk.2.1]; exact h28)
      (by rw [hk.2.2.1]; exact h29) (by rw [hk.2.2.2]; exact h18) hkm2 hz hng hcan (by omega) hval hnn
      (NatSqr.IntAt.keep hB.z0h fun x m h1 h2 => hrd x m (by omega) (by omega) (Or.inr (by omega)))
      (NatSqr.IntAt.keep hB.z2h fun x m h1 h2 => hrd x m (by omega) (by omega) (Or.inr (by omega))) hK

end FvModexp.Arm64.NatMul
