import FvModexp.Proofs.Amd64.Exp.P2W2BJ
import FvModexp.Proofs.Amd64.Exp.P2W2Fin
import FvModexp.Proofs.Amd64.Exp.P2W2Tl2
import FvModexp.Proofs.Amd64.Exp.P2W2R1

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the final `norm`, the deferred closure and `RET` (agent divmc s74; amd64 twin
of agent infra's `Arm64.P2W2X1`)

`nmT`: from `nH` = fn+0x8e0 (`z = (R8, SI, R15)` a U-class buffer holding `v` in its first `l` words, `l ≤ c`): the
inline `z.norm()` loop, the bounds check, the result stores, the deferred `stk.restore`, `RET` (`fin`) and `finQ` →
the function's post `FQ` (nat.go:1264).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open FvModexp.Amd64.ExpHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the final `norm` + closure + `RET`** -/
theorem nmT (hap : Amd64.ImplApart Extracted.program impl) (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}
    (hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {zzp tp p l c v cst : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp tp lm p c) (hlc : l ≤ c) (hv : natVal M p l = v) (hbud : b - cst ≤ b1)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 nH) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) (h8 : S.regs 8 = BitVec.ofNat 64 p) (h6 : S.regs 6 = BitVec.ofNat 64 l)
    (h15 : S.regs 15 = BitVec.ofNat 64 c) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b L K zp zc st v cst s) := by
  have hc40 := hub.c40
  have hp64 : p < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rcases hub.org with ⟨rfl, -⟩ | ⟨h1, -⟩
      · exact hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · omega
    · have := (hub.live h0).2.2.2; omega
  have hpa : l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true) := by
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    · obtain ⟨-, -, hacc, h48⟩ := hub.live (by omega)
      exact Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_weaken _
        (Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega))⟩
  have hrs : ResSep s.mem M st p c := fun hc hn => by
    rcases hub.rs hc (hw.ain hn).2 with ⟨rfl, rfl⟩ | h
    · exact rs_z hP hw hc hn
    · exact h
  have hres : NatOF R L L1 M zp zc 1 p (Expmc.normL M p l) c v := by
    refine ⟨?_, Expmc.normL_norm M p l, Nat.le_trans (Expmc.normL_le M p l) hlc, hc40, hub.live,
      hub.org.imp id fun h => ⟨by omega, h.2⟩⟩
    rw [← hv]; exact Expmc.normL_val M p l
  exact ReachesRet.mono (fin hap sp g st (stLen s.mem st) bp r p c s.fsBase M hc40 hp64 (tenv_of hP hw hsl) l S hpc
    hsp h14 hfs hx15 hdf h8 h6 h15 hm hlc hpa) (fun s' ht => finQ hP hw hres hrs hbud ht)

end

end FvModexp.Amd64.P2W2
