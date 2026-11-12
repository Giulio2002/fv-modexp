import FvModexp.Proofs.Arm64.Exp.P2W4R1b
import FvModexp.Proofs.Arm64.Exp.P2W4Sk
import FvModexp.Proofs.Arm64.Exp.P2W4AT
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): after the table — skip loop, and the `return 1` exit (agent infra)

`afterTable`: from `AT` at `1793424`, the skip-zero segment (`skipHead`/`skipLoop`); its `return 1` exit is closed
here (`r1all`, value `1 = x^y mod 2^logM` by `Exp.p2win_correct`), its `bitLen` exit is the continuation `KB`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.ExpHyp

/-- `p2win` with `len y = yl` unfolds to the skip loop of `i0`/`yi0` -/
theorem p2win_eq (lm yl X Y : Nat) (hn : Exp.nlen Y = yl) :
    Exp.p2win 2 lm X Y = match Exp.skipZero Y (i0 lm yl) (yi0 lm yl Y) with
      | none => 1
      | some (i, yi) => Exp.winRun 2 (fun z d => Exp.iter (fun z => z * z % 2 ^ lm) 2 z * Exp.p2Pow lm X d % 2 ^ lm)
          (Exp.p2Pow lm X) Y i yi := by
  unfold Exp.p2win; simp only [hn, i0, yi0]; rfl

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- the words of `y` at a later memory -/
theorem y_words (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd (natVal s.mem yp yl) j := by
  intro j hj
  have hyO : OE R L sp K st s.mem yp (8 * yl) := hP.2.2.2.2.2.2.2.1
  have hb := oe_bytes hP hyO (fun hc => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc).2.2.2.2.2.2.1)
  rw [h.readB (hyO.1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
    fun i hi => by rw [Nat.add_assoc]; exact hb (8 * j + i) (by omega)]
  exact Expmc.readLE_wd s.mem yp j yl hj

set_option maxRecDepth 20000 in
/-- **after the table**: skip loop; `return 1` closed, `bitLen` exit = `KB` -/
theorem afterTable {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract (LibW.program.link impl) noE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {L3 : List (Nat × Nat)} {b3 zzp bp : Nat}
    (hAT : AT R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M L3 b3 zzp bp) {c0 cst : Nat}
    (hb3 : b - c0 ≤ b3) (hcst : c0 + allocCost 8 ≤ cst) (hcb : cst ≤ b)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (hX : natVal s.mem xp xl % 2 = 1) (hY : 0 < natVal s.mem yp yl) (r29 : BitVec 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1793424) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (KB : KBl impl (s.regs 30)
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s) sp g lm yp yl M (s.regs 18) r29
      (Exp.skipZero (natVal s.mem yp yl) (i0 lm yl) (yi0 lm yl (natVal s.mem yp yl)))) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) cst s) := by
  have hw := hAT.wc
  have hsl := hAT.esl
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hwacc : M.accessible (sp - K) (K + 848) true = true := by
    rw [hw.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.2.1
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.2.1
  have hya : M.accessible yp (8 * yl) false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.2.2.2.2.2.1
  have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.1
  have hyN : NatNorm s.mem yp yl := hP.2.2.2.2.2.2.2.2.2.2.1
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r816, r824, r840, -⟩ := hsl
  refine skipHead _ _ sp g lm yp yl (natVal s.mem yp yl) M (s.regs 18) r29 hal hlm2 hlm hyl0 hsp2 (y_words hP hw) hya
    hy48 hyl (Memory.accessible_mono _ (Memory.accessible_weaken _ hwacc) (show sp - K ≤ sp + 816 by omega)
      (show sp + 816 + 32 ≤ sp - K + (K + 848) by omega)) r816 r824 r840 KB ?_ S hpc hsp h28 h29 h18 hm
  intro S' e1 e2 e3 e4 e5 e6 e7 hv
  have hval : natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm = 1 := by
    rw [← Exp.p2win_correct 2 lm _ _ (Or.inl rfl) hX hY hlm2, p2win_eq lm yl _ _ (SubMod2N.norm_nlen _ _ _ hyN), hv]
  rw [hval]
  exact r1all hap hmk hno hP hw hAT.esl hr4 hr48 (by omega) (by omega) S' e1 e2 e5 e3 e7 e6

end

end FvModexp.Arm64.P2W4
