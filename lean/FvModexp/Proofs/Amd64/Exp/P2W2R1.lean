import FvModexp.Proofs.Amd64.Exp.P2W2Fin
import FvModexp.Proofs.Amd64.Exp.P2W2Seg
import FvModexp.Proofs.Amd64.Exp.P2W2Tl2
import FvModexp.Proofs.Amd64.Exp.P2W2Sk

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): `return z.setWord(1)`, `cap z ≠ 0` (nat.go:1187-1192, nat.go:58-76)
(agent divmc s70; amd64 twin of agent infra's `Arm64.P2W2R1`)

From `r1E` (fn+0x32a): `z ≠ nil` (`TESTQ SI` at +0x332), `cap z ≠ 0` (`TESTQ DI` at +0x340, `JNE +0x361`):
`z[0] = 1` at +0x361, then `tS` (fn+0x368; `tailS`) and the post `FQ` with value `1` (`finQ`).
Also `rs_z` / `rs_live` (the amd64 twins of `Arm64.P2W2.rs_z` / `rs_live`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open FvModexp.Amd64.ExpHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

/-- `ResSep` for the entry `z` -/
theorem rs_z (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) : ResSep s.mem M st zp zc := by
  intro hc hn
  rcases hw.kf with h | ⟨hin, hap⟩
  · exact absurd h hn
  · obtain ⟨⟨hzO1, -, -, -⟩, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc
    rcases hzO1 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart at this ⊢; omega
    · exact (hin.apart hO)

/-- `ResSep` for a result apart from every element of the live set `L1` of `WC` -/
theorem rs_live (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {p c : Nat} (hap : ApartAll p (8 * c) L1) :
    ResSep s.mem M st p c := by
  intro hc hn
  have := hap _ (hw.ain hn).1
  simp only at this
  rwa [show stW M st + 8 * stCap M st - stW M st = 8 * stCap M st by omega] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z ≠ nil`, `cap z ≠ 0`: `z[0] = 1` in place -/
theorem r1a {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {cst : Nat} (hb : b - cst ≤ b1)
    (hzp : zp ≠ 0) (hzc : 0 < zc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 r1E) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b L K zp zc st 1 cst s) := by
  obtain ⟨⟨hzO1, hzO2, hzO3, -⟩, hzacc, hz48, hz8, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hzc
  have hzp64 : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc40 : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, r1f0, r200, -⟩ := hsl
  have hzaM : M.accessible zp 8 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := (hw.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have hz0 : ¬ (zp = 0) := hzp
  have hc0 : ¬ (zc = 0) := by omega
  unfold Apart at hzO2 hzO3
  subst hm
  refine SegProg.lift P2W2Seg.codeIn (r := BitVec.ofNat 64 tS) ?_
  janus64_run [r1f0, r200, hzaM, hwaccF, hz0, hc0] until [tS]
  have hF1 : MemFrame S.mem (S.mem.writeLE zp 8 1) [(zp, zp + 8)] :=
    (MemFrame.refl _ _).writeLE_inRanges _ ⟨(zp, zp + 8), by simp, by simp only; omega, by simp only; omega⟩
  have hzH : InRanges zp (8 * zc) L1 ∨ Outside zp (8 * zc) R.rt := hw.le.held hzO1
  have hw' : WC R H L K g sp st zp zc s.mem (S.mem.writeLE zp 8 1) L1 b1 ℓ := by
    refine hw.frame hF1 (by simp only [Janus.Arm64.Memory.regions_writeLE]) (fun a k ho => ?_) (fun a k _ ho => ?_) ?_ ?_
    · simp only [ZS, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [ZS, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show zp + 8 - zp = 8 by omega]
      exact hzH.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega))
  have hsl' : ESl (S.mem.writeLE zp 8 1) sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) :=
    ESl.keep hsl0 (fun a k ha => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega))
  have hres : NatOF R L L1 (S.mem.writeLE zp 8 1) zp zc 1 zp 1 zc 1 := by
    refine ⟨?_, Or.inr ?_, by omega, hzc40, fun _ => ⟨hz8, hzH, ?_, hz48⟩, Or.inl ⟨rfl, rfl⟩⟩
    · show (S.mem.writeLE zp 8 1).readLE zp (8 * 1) = 1
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
    · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hw.fr.accessible]; exact hzacc
  refine ReachesRet.mono (tailS hap _ sp g st (stLen s.mem st) bp r zp zc s.fsBase (S.mem.writeLE zp 8 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega) ?_ ?_ (by omega) (tenv_of hP hw' hsl'))
    (fun s' ht => finQ hP hw' hres (rs_z hP hw') hb ht)
  all_goals first
    | exact hfs
    | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact Janus.Arm64.Memory.accessible_weaken _ hzaM)
    | janus64_simp

end

end FvModexp.Amd64.P2W2
