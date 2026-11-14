import FvModexp.Proofs.Amd64.Exp.P2W4Cp4
import FvModexp.Proofs.Amd64.Exp.P2W4R1b
import FvModexp.Proofs.Common.ExpPow2
import FvModexp.Proofs.Common.SubMod2NMath
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): from the table to the loop test (agent divmc s77, port of divmc s71; amd64 twin of agent infra's
`Arm64.P2W4Ret1.afterTable` + `Arm64.P2W4Cp5`)

`afterTable`: from `AT` at the table's return (fn+0x295): `skipHead` (skip loop); `return 1` closed by `r1all`, the
`bitLen` exit is a `KBl` continuation. `afterT`: the `bitLen` exit closed by `blH` (first window); the continuation is
the loop invariant's `KL` for every `kk` with the target value `x^y mod 2^logM`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- (as `Arm64.P2W4.p2win_eq`) -/
theorem p2win_eq (lm yl X Y : Nat) (hn : Exp.nlen Y = yl) :
    Exp.p2win 4 lm X Y = match Exp.skipZero Y (i0 lm yl) (yi0 lm yl Y) with
      | none => 1
      | some (i, yi) => Exp.winRun 4 (fun z d => Exp.iter (fun z => z * z % 2 ^ lm) 4 z * Exp.p2Pow lm X d % 2 ^ lm)
          (Exp.p2Pow lm X) Y i yi := by
  unfold Exp.p2win; simp only [hn, i0, yi0]; rfl

theorem skipZero_le (y : Nat) : ∀ i yi i' yi', Exp.skipZero y i yi = some (i', yi') → i' ≤ i := by
  intro i
  induction i with
  | zero => intro yi i' yi' h; unfold Exp.skipZero at h; split at h <;> simp_all
  | succ i ih =>
    intro yi i' yi' h
    unfold Exp.skipZero at h
    split at h
    · simp at h; omega
    · have := ih _ _ _ h; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

/-- the words of `y` at a later memory -/
theorem y_words (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd (natVal s.mem yp yl) j := by
  intro j hj
  have hyO : OE R L sp K st s.mem yp (8 * yl) := hP.2.2.2.2.2.2.1
  have hb := oe_bytes hyO (fun hc => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc).2.2.2.2.2.2.2.1)
  rw [h.readB (hyO.1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
    fun i hi => by rw [Nat.add_assoc]; exact hb (8 * j + i) (by omega)]
  exact Expmc.readLE_wd s.mem yp j yl hj

set_option maxRecDepth 20000 in
/-- **after the table**: skip loop; `return 1` closed, `bitLen` exit = `KB` -/
theorem afterTable {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {L3 : List (Nat × Nat)} {b3 zzp tp : Nat}
    (hAT : AT R L K g sp st bp r zp zc xp xl xc yp yl lm s M L3 b3 zzp tp) {c0 cst : Nat}
    (hb3 : b - c0 ≤ b3) (hcst : c0 + allocCost 8 ≤ cst) (hcb : cst ≤ b)
    (hX : natVal s.mem xp xl % 2 = 1) (hY : 0 < natVal s.mem yp yl) (r5 : W64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6198613) (hKp : Kp sp g r5 s.fsBase false M S)
    (KB : KBl impl (BitVec.ofNat 64 r)
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s) sp g lm yp yl M r5 s.fsBase false
      (Exp.skipZero (natVal s.mem yp yl) (i0 lm yl) (yi0 lm yl (natVal s.mem yp yl)))) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s) := by
  have hw := hAT.wc
  have hsl := hAT.esl
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := (hw.cenv hP).2.2.2.1
  have hsp48 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := (hw.cenv hP).2.2.1
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.1
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.1
  have hya : M.accessible yp (8 * yl) false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.2.2.2.2.1
  have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.1
  have hyN : NatNorm s.mem yp yl := hP.2.2.2.2.2.2.2.2.2.1
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r1d8, r1e0, r228, -⟩ := hsl0
  refine skipHead _ _ sp g lm yp yl (natVal s.mem yp yl) M r5 s.fsBase false (by omega) hlm2 hlm hyl0
    (y_words hP hw) hya hy48 hyl
    (Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_weaken _ hwacc) (by omega) (by omega))
    (Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_weaken _ hwacc) (by omega) (by omega))
    r1d8 r1e0 r228 KB ?_ S hpc hKp
  rintro S' e1 ⟨e2, e3, -, e5, e6, e7, e8⟩ hv
  have hval : natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm = 1 := by
    rw [← Exp.p2win_correct 4 lm _ _ (Or.inr rfl) hX hY hlm2, p2win_eq lm yl _ _ (SubMod2N.norm_nlen _ _ _ hyN), hv]
  rw [hval]
  exact r1all hap hmk hno hP hw hsl (by omega) (by omega) S' e1 e2 e3 e6 e5 e7 e8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **from the table's return to the loop test** (see the module doc) -/
theorem afterT {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {L3 : List (Nat × Nat)} {b3 zzp tp : Nat}
    (hAT : AT R L K g sp st bp r zp zc xp xl xc yp yl lm s M L3 b3 zzp tp) {c0 cst : Nat}
    (hb3 : b - c0 ≤ b3) (hcst : c0 + allocCost 8 ≤ cst) (hcb : cst ≤ b)
    (hcst2 : c0 + 2 * P2Pre.tC lm + 16 * min yl ((lm - 2) / 64 + 1) * bc lm ≤ cst)
    (hX : natVal s.mem xp xl % 2 = 1) (hY : 0 < natVal s.mem yp yl) (r5 : W64)
    (KL : ∀ kk, KL impl (BitVec.ofNat 64 r)
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s)
      R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6198613) (hKp : Kp sp g r5 s.fsBase false M S) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s) := by
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.1
  have hyN : NatNorm s.mem yp yl := hP.2.2.2.2.2.2.2.2.2.1
  refine afterTable hap hmk hno hP hAT hb3 hcst hcb hX hY r5 S hpc hKp ?_
  intro S' i yi e1 e2 e3 e4 e5 e6 e7 hi hyi0 hyi hv
  have hii := skipZero_le _ _ _ _ _ hv
  have hi0 : i ≤ min (yl - 1) ((lm - 2) / 64) := by simp only [i0] at hii; omega
  obtain ⟨hk1, hk32, -⟩ := kk_facts yi hyi0 hyi
  have hmul : (kkOf yi - 1 + 16 * i) * bc lm ≤ 16 * min yl ((lm - 2) / 64 + 1) * bc lm :=
    Nat.mul_le_mul_right _ (by omega)
  refine blH hmv hmk _ _ hP KL (CPF.ofAT hAT) S' i yi e1 e2 e3 e4 e5 e6 e7 hi hyi0 hyi hX
    (by omega) (by omega) ?_
  rw [← Exp.p2win_correct 4 lm _ _ (Or.inr rfl) hX hY hlm2, p2win_eq lm yl _ _ (SubMod2N.norm_nlen _ _ _ hyN), hv]
  simp only [Exp.winRun, Exp.B, kkOf, show (64 : Nat) / 4 = 16 by rfl, show (4 : Nat) - 1 = 3 by rfl]

end

end FvModexp.Amd64.P2W4
