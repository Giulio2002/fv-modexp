import FvModexp.Proofs.Arm64.Exp.ModInvDefs

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the Q-form statement pieces + the level-cost bridge (agent infra, s45)

TIGHT COSTS (NOTES-conventions "[infra s44] … Q-form PLAN"): the Hensel rounds call `nat.sqr` / `nat.mul` in Q-form
(divmc's `SqrHypQ` / `MulHypQ`) at ONE reserve level `H` per call.
* `PreQ … H … B`: `ModInv.Pre` with the REAL budget `B` (`R.inv B`) and the cost slot
  `(stLen s.mem st + D n ≤ H ∧ cost sqrC mulC xl n + stkR H s.mem st ≤ B)`;
  `PostQ`: `B − (cost + stkR H s.mem st) + stkR H s'.mem st ≤ b'` (divmc's Q shape).
* `PreL … ℓ b` / `PostL`: the bridged old level-cost shape (`H := ℓ + D n`, `ℓ = stLen s.mem st`):
  post `b − (cost + stkRes (ℓ + D n)) ≤ b'`.
* `pre_of_Q` / `post_of_Q`: `PreQ` ↔ `Pre` at the effective budget `B − stkR H s.mem st` (the internal proofs' form).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut NatRes NatOF RtPost StackOK' stWs)

/-- the Q-form pre (real budget `B`) -/
@[reducible] def PreQ (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (B : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  CallEnv R L s (K kc) A ∧ Serves R ∧
    (RunIface.Globals R s.mem (winA s (K kc) A) ∧ Outside RunIface.gA 32 ([(zp, zp + 8 * zc)] ++ stWs s.mem st)) ∧
    1 ≤ n ∧ n ≤ 2 ^ 15 ∧ zl ≤ zc ∧ zp < 2 ^ 64 ∧ 0 < zc ∧ WrOut R L s (K kc) A zp zc ∧
    0 < xl ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧ xl ≤ 2 ^ 12 ∧ RdIn R L s (K kc) A xp xl ∧ NatNorm s.mem xp xl ∧
    natVal s.mem xp xl % 2 = 1 ∧ (0 < zc → Apart zp (8 * zc) xp (8 * xc)) ∧
    StkIn R L s (K kc) A st ∧ stLen s.mem st + 8 * NW n + 72 ≤ 2 ^ 16 ∧
    StkApart s.mem st zp (8 * zc) ∧ StkApart s.mem st xp (8 * xl) ∧
    (stLen s.mem st + D n ≤ H ∧ cost sqrC mulC xl n + stkR H s.mem st ≤ B) ∧
      R.inv B L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ Outside NatAdd.wordT 16 R.rt ∧
    (OneIn R L s kc zp zc st ∧ PX R L s zp zc st xp xl xc)

/-- the result facts with a budget relation `bud b'` (shared by `PostQ` / `PostL`) -/
@[reducible] def PostB (R : RtInv) (kc : Nat) (bud : State → Nat → Prop)
    (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s s' : State) : Prop :=
  ∃ p' l' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = l' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' l' = val (natVal s.mem xp xl) n ∧ NatNorm s'.mem p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ bud s' b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p' c'

/-- the Q-form post -/
@[reducible] def PostQ (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (B : Nat)
    (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s s' : State) : Prop :=
  PostB R kc (fun s' b' => B - (cost sqrC mulC xl n + stkR H s.mem st) + stkR H s'.mem st ≤ b') L zp zc st xp xl n s s'

/-- the bridged level-cost pre (`H := ℓ + D n`, `ℓ` = the entry stack length) -/
@[reducible] def PreL (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (ℓ b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  PreQ R kc (ℓ + D n) sqrC mulC b L zp zl zc st xp xl xc n s ∧ stLen s.mem st = ℓ

/-- the bridged level-cost post: one reserve `stkRes (ℓ + D n)` charged -/
@[reducible] def PostL (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (ℓ b : Nat)
    (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s s' : State) : Prop :=
  PostB R kc (fun _ b' => b - (cost sqrC mulC xl n + stkRes (ℓ + D n)) ≤ b') L zp zc st xp xl n s s'

section
variable {R : RtInv} {kc H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {B : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

/-- `PreQ` gives the internal `Pre` at the effective budget `B − stkR H s.mem st` -/
theorem pre_of_Q (h : PreQ R kc H sqrC mulC B L zp zl zc st xp xl xc n s) :
    Pre R kc H sqrC mulC (B - stkR H s.mem st) L zp zl zc st xp xl xc n s := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21,
    ⟨c22, c23⟩, c24, c25⟩ := h
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21,
    ⟨c22, by omega⟩, ?_, c25⟩
  rw [Nat.sub_add_cancel (by omega)]; exact c24

/-- the internal `Post` at the effective budget is the Q-form post -/
theorem post_of_Q {s' : State} (h : Post R kc H sqrC mulC (B - stkR H s.mem st) L zp zc st xp xl n s s') :
    PostQ R kc H sqrC mulC B L zp zc st xp xl n s s' := by
  obtain ⟨p', l', c', e0, e1, e2, hv, hN, hlc, hc, L', b', hx, hb, rest⟩ := h
  exact ⟨p', l', c', e0, e1, e2, hv, hN, hlc, hc, L', b', hx, by omega, rest⟩

/-- the bridge: a Q-form post at `H = ℓ + D n` is a level-cost post -/
theorem postL_of_Q {ℓ : Nat} {s' : State} (h : PostQ R kc (ℓ + D n) sqrC mulC B L zp zc st xp xl n s s') :
    PostL R kc sqrC mulC ℓ B L zp zc st xp xl n s s' := by
  obtain ⟨p', l', c', e0, e1, e2, hv, hN, hlc, hc, L', b', hx, hb, rest⟩ := h
  have := stkR_le (ℓ + D n) s.mem st
  exact ⟨p', l', c', e0, e1, e2, hv, hN, hlc, hc, L', b', hx, by omega, rest⟩

end

end FvModexp.Arm64.ModInv
