import FvModexp.Proofs.Arm64.Exp.P2W2Fin
import FvModexp.Proofs.Arm64.Exp.P2W2Al
import FvModexp.Proofs.Arm64.Exp.P2W2R1

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `return z.setWord(1)` with `cap z = 0` (`makeslice(Word, 1, 1)`) and
`return nat{1}` (`z == nil`, `newobject([1]Word)`) (nat.go:1187-1192, nat.go:58-63) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.ExpHyp

abbrev mkE : Nat := 587344
abbrev noE : Nat := 186784
theorem mkE_eq : Extracted.program.contractAddr "runtime.makeslice" = mkE := by decide
theorem noE_eq : Extracted.program.contractAddr "runtime.newobject" = noE := by decide

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z ≠ nil`, `cap z = 0`: `makeslice(Word, 1, 1)`, `[0] = 1` -/
theorem r1b {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm (stLen s.mem st))
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {cst : Nat}
    (hbc : allocCost 8 ≤ b1) (hb : b - cst ≤ b1 - allocCost 8)
    (hzp : zp ≠ 0) (hzc : zc = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1795700) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hm : S.mem = M) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S (FQ R b L K zp zc st 1 cst s) := by
  have hzp64 : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hwacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [hw.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, r472, r488, -⟩ := hsl
  subst hzc hm
  have hrd : blockSize 8 true ≤ allocCost 8 := blockSize_le_allocCost 8 true
  janus_run [r472, r488] until [mkE]
  refine mkCall mkE_eq hmk _ _ hP hw (n := 1) (c := 1) (ra := 1795740) (by decide) (by decide) (by decide) (by decide)
    (by decide) (Nat.le_trans hrd hbc) _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun ptr junk f1 v1 m1 ex1 ep1 hA => ?_)
  all_goals first | (janus_simp; done) | skip
  obtain ⟨hw', hsl', hres⟩ := fresh1 hP hA hw.le hsl0
  have hacc1 : m1.accessible ptr.toNat 8 true = true := Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by have := hA.sz; omega)
  have hb48 := hA.b48
  have hsz := hA.sz
  have hrc : blockSize (8 * 1) true ≤ allocCost 8 := hA.rc
  clear hA
  janus_run [hacc1] until [tB]
  rw [show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
  refine tailB hap _ _ sp g st (stLen s.mem st) ptr.toNat 1 1 (s.regs 30).toNat (s.regs 18) (s.regs 29)
    (m1.writeLE ptr.toNat 8 1) rfl rfl ?_ ?_ ?_ ?_ ?_ rfl ptr.isLt (by decide) (by decide)
    (tenv_of hP hw' hsl' hr4 hr48) (fun s' ht => finQ hP hw' hres (by omega) ht)
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z == nil`: `newobject([1]Word)`, `[0] = 1` -/
theorem r1c {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hno : NewobjectLiveContract (LibExp.program.link impl) noE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm (stLen s.mem st))
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {cst : Nat}
    (hbc : allocCost 8 ≤ b1) (hb : b - cst ≤ b1 - allocCost 8)
    (hzp : zp = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1795700) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hm : S.mem = M) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S (FQ R b L K zp zc st 1 cst s) := by
  have hzp64 : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hwacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [hw.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, r472, r488, -⟩ := hsl
  subst hzp hm
  have hrd : blockSize 8 true ≤ allocCost 8 := blockSize_le_allocCost 8 true
  janus_run [r472, r488] until [noE]
  refine noCall noE_eq hno _ _ hP hw (ra := 1795772) (by decide) (by decide)
    (Nat.le_trans hrd hbc) _ rfl ?_ ?_ ?_ ?_ ?_ (fun ptr junk f1 v1 m1 ex1 ep1 hA => ?_)
  all_goals first | (janus_simp; done) | skip
  obtain ⟨hw', hsl', hres⟩ := fresh1 hP hA hw.le hsl0
  have hacc1 : m1.accessible ptr.toNat 8 true = true := Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by have := hA.sz; omega)
  have hb48 := hA.b48
  have hsz := hA.sz
  have hrc : blockSize 8 true ≤ allocCost 8 := hA.rc
  clear hA
  janus_run [hacc1] until [tN]
  rw [show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
  refine tailN hap _ _ sp g st (stLen s.mem st) ptr.toNat (s.regs 30).toNat (s.regs 18) (s.regs 29)
    (m1.writeLE ptr.toNat 8 1) rfl rfl ?_ ?_ ?_ rfl ptr.isLt
    (tenv_of hP hw' hsl' hr4 hr48) (fun s' ht => finQ hP hw' hres (by omega) ht)
  all_goals janus_simp

/-- **`return 1`** from `r1E` (all three shapes) -/
theorem r1all {impl : List Segment} (hap : ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract (LibExp.program.link impl) noE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm (stLen s.mem st))
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {cst : Nat}
    (hbc : allocCost 8 ≤ b1) (hb : b - cst ≤ b1 - allocCost 8)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1795700) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h7 : S.regs 7 = 1#64) (hm : S.mem = M) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S (FQ R b L K zp zc st 1 cst s) := by
  by_cases hzp : zp = 0
  · exact r1c hap hno hP hw hsl hr4 hr48 hbc hb hzp S hpc hsp h18 h28 hm
  by_cases hzc : zc = 0
  · exact r1b hap hmk hP hw hsl hr4 hr48 hbc hb hzp hzc S hpc hsp h18 h28 hm
  · exact r1a hap hP hw hsl hr4 hr48 (by omega) hzp (by omega) S hpc hsp h18 h28 h7 hm

end

end FvModexp.Arm64.P2W2
