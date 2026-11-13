import FvModexp.Proofs.Amd64.NatQ.KMulB
import FvModexp.Proofs.Amd64.NatQ.KSqrPQ

set_option autoImplicit false

/-!
# [amd64 port (divmc s51) of the Q-form Arm64/NatQ/KMulPD.lean — TIGHT COSTS] `karatsuba` (amd64): the prologue's memory facts (natmul.go:164-206)

`KQm … s M`: the facts of the prologue's memory `M` before the `stk.nat` call: `KPre` at the entry, the stack arguments
`y = (yp, n, yc)` at `RSP + 8 … RSP + 32`, only our frame written (`[RSP-448, RSP)`, the spills `[RSP+32, RSP+72)`),
the saved `RBP` (at `RSP - 8`) and the spills `RSP + 40 := zp`, `RSP + 64 := xp`. The prologue segment modules
(`KMulPA`, `KMulPB`, `KMulPC`) import this one only. Word lemmas: `NatSqr.kmask`/`kand2`/`kshr1`/`kshl3`/`kshl4`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

/-- the prologue memory facts (see the module doc) -/
structure KQm (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (M : Memory) : Prop where
  pre : KPre R b H L W st zp (2 * n) zc xp n xc yp n yc s
  y8 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp
  y16 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  y24 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc
  fr : MemFrame s.mem M [((s.regs 4).toNat - 448, (s.regs 4).toNat), ((s.regs 4).toNat + 32, (s.regs 4).toNat + 72)]
  reg : M.regions = s.mem.regions
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  s2 : M.readLE ((s.regs 4).toNat + 40) 8 = zp
  s5 : M.readLE ((s.regs 4).toNat + 64) 8 = xp

/-- the stack arguments through the prologue's writes -/
theorem KQm.yrd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {M : Memory} (h : KQm R b H L W st zp zc xp n xc yp yc s M) :
    M.readLE ((s.regs 4).toNat + 8) 8 = yp ∧ M.readLE ((s.regs 4).toNat + 16) 8 = n ∧
      M.readLE ((s.regs 4).toNat + 24) 8 = yc := by
  have hrd : ∀ k, 8 ≤ k → k + 8 ≤ 32 → M.readLE ((s.regs 4).toNat + k) 8 = s.mem.readLE ((s.regs 4).toNat + k) 8 :=
    fun k h1 h2 => h.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact ⟨(hrd 8 (by omega) (by omega)).trans h.y8, (hrd 16 (by omega) (by omega)).trans h.y16,
    (hrd 24 (by omega) (by omega)).trans h.y24⟩

end FvModexp.Amd64.Q.NatMul
