import FvModexp.Proofs.Arm64.Exp.ModInvQDefs
import FvModexp.Proofs.Arm64.Exp.RAx30

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the row-level Q-form pre WITHOUT the `X30` conjuncts (agent infra s49)

`PreQR` = `PreQ` without `X30 % 4 = 0 ∧ X30 < 2^48` (final-gate RA rule, BRIEF "RETURN-ADDRESS PIN GAP"); the row
re-derives them from the ABI with `RAx30.ens_drop`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut NatRes NatOF RtPost StackOK' stWs)

/-- `PreQ` without the `X30` conjuncts -/
@[reducible] def PreQR (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (B : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  CallEnv R L s (K kc) A ∧ Serves R ∧
    (RunIface.Globals R s.mem (winA s (K kc) A) ∧ Outside RunIface.gA 32 ([(zp, zp + 8 * zc)] ++ stWs s.mem st)) ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ zp < 2 ^ 64 ∧ 0 < zc ∧ WrOut R L s (K kc) A zp zc ∧
    0 < xl ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧ xl ≤ 2 ^ 12 ∧ RdIn R L s (K kc) A xp xl ∧ NatNorm s.mem xp xl ∧
    natVal s.mem xp xl % 2 = 1 ∧ (0 < zc → Apart zp (8 * zc) xp (8 * xc)) ∧
    StkIn R L s (K kc) A st ∧ stLen s.mem st + 8 * NW n + 72 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st xp (8 * xl) ∧
    (stLen s.mem st + D n ≤ H ∧ cost sqrC mulC xl n + stkR H s.mem st ≤ B) ∧
      R.inv B L (s.regs 28).toNat (view R.rt L s.mem) ∧ Outside NatAdd.wordT 16 R.rt ∧
    (OneIn R L s kc zp zc st ∧ PX R L s zp zc st xp xl xc)

theorem PreQR.toQ {R : RtInv} {kc H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {B : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (h : PreQR R kc H sqrC mulC B L zp zl zc st xp xl xc n s) (h1 : (s.regs 30).toNat % 4 = 0)
    (h2 : (s.regs 30).toNat < 2 ^ 48) : PreQ R kc H sqrC mulC B L zp zl zc st xp xl xc n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    h1, h2, a24, a25, a26⟩

end FvModexp.Arm64.ModInv
