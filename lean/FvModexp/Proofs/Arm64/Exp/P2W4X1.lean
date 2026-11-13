import FvModexp.Proofs.Arm64.Exp.P2W4BJ
import FvModexp.Proofs.Arm64.Exp.P2W4Fin

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the final `norm`, the deferred closure and `RET` (agent infra)

`nmT`: from `0x1b62ac` (`z = (R0, R1, R13)` a U-class buffer holding a normalised odd value `v`): the inline
`z.norm()` (one test: the top word is non-zero), the bounds check `len ≤ cap`, then `tailA` (result stores, the
deferred `stk.restore`, `RET`) and `finQ` → the function's post `FQ` (nat.go:1264).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.ExpHyp

/-- the norm loop's head -/
abbrev nmE : Nat := 1794732

section
variable {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the final `norm` + closure + `RET`** -/
theorem nmT (hap : ImplApart Extracted.program impl) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm (stLen s.mem st))
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {zzp bp p l c v cst : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp bp lm p c) (hv : NV M p l c v) (hbud : b - cst ≤ b1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 nmE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 l) (h13 : S.regs 13 = BitVec.ofNat 64 c) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S (FQ R b L K zp zc st v cst s) := by
  obtain ⟨hlc, hval, hN, hodd⟩ := hv
  have hl0 : 0 < l := len_pos hval hodd
  have hc0 : 0 < c := by omega
  have hc40 := hub.c40
  obtain ⟨-, -, hacc, h48⟩ := hub.live hc0
  have hz : M.readLE (p + (l - 1) * 8) 8 ≠ 0 := by
    rcases hN with h | h
    · omega
    · rw [Nat.mul_comm]; exact h
  have hacc1 : M.accessible (p + (l - 1) * 8) 8 false = true :=
    Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
  have hsub : BitVec.ofNat 64 l - 1#64 = BitVec.ofNat 64 (l - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have he := tenv_of hP hw hsl hr4 hr48
  have hrs : ResSep s.mem M st p c := fun hc hn => by
    rcases hub.rs hc (hw.ain hn).2 with ⟨rfl, rfl⟩ | h
    · exact rs_z hP hw hc hn
    · exact h
  have hret : BitVec.ofNat 64 (s.regs 30).toNat = s.regs 30 := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  subst hm
  janus_run [hz, hacc1, hsub] until [tA]
  rw [← hret]
  refine tailA hap _ _ sp g st (stLen s.mem st) p l c (s.regs 30).toNat (s.regs 18) (s.regs 29) S.mem rfl ?_ ?_ ?_
    ?_ ?_ ?_ rfl (by omega) (by omega) (by omega) he fun s' ht =>
      finQ hP hw ⟨hval, hN, hlc, hc40, hub.live, hub.org.imp id fun h => ⟨by omega, h.2⟩⟩ hrs hbud ht
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W4
