import FvModexp.Proofs.Arm64.Exp.ModInvNewton

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the join-point statements (agent infra)

The function is a chain of segment lemmas over the entry state `s` (precondition `Pre`), each ending in the statement
of the next join as a hypothesis, so the segment modules compile in parallel:
* entry → the Newton loop → `JS` (`+0x64`, `n ≤ 64`) or `J0` (`+0x6c`, `n > 64`);
* `JS` → return: `k0 &= 1<<n - 1; return z.setWord(k0)` (the `n ≤ 64` test at `+0x64` included: the mask's
  `CSEL` reads its flags).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

/-- what the function promises, from a state `S` inside its frame (entry state `s`) -/
@[reducible] def Goal (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s S : State) : Prop :=
  ReachesRet (LibW.program.link impl) (s.regs 30) S (fun s' =>
    (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
      Post R kc sqrC mulC b L zp zc st xp xl n s s')

/-- the saved LR / FP -/
@[reducible] def Fw0 (s : State) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat ∧ M.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat

/-- `k0` after the Newton loop (nat.go:1293-1300) -/
@[reducible] def k0 (s : State) (xp xl n : Nat) : Nat := Exp.newton (min 64 n) (natVal s.mem xp xl % Exp.B)

/-- **JS** (`+0x64`, the Newton loop's exit, `n ≤ 64`): `X0 = z.ptr`, `X2 = cap z`, `X7 = n`, `X10 = k0`; only
stack stores so far -/
def JS (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ S : State, Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s → n ≤ 64 →
    S.pc = BitVec.ofNat 64 (1797104 + 0x64) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 240) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 2 = BitVec.ofNat 64 zc → S.regs 7 = BitVec.ofNat 64 n →
    S.regs 10 = BitVec.ofNat 64 (k0 s xp xl n) →
    MemFrame s.mem S.mem (winA s (K kc) A) → S.mem.regions = s.mem.regions → Fw0 s S.mem →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

/-- **J0** (`+0x6c`, `n > 64`): the arguments in `X0, X2 … X7`, `X10 = k0`; only stack stores so far -/
def J0 (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ S : State, Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n →
    S.pc = BitVec.ofNat 64 (1797104 + 0x6c) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 240) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 2 = BitVec.ofNat 64 zc → S.regs 3 = BitVec.ofNat 64 st →
    S.regs 4 = BitVec.ofNat 64 xp → S.regs 5 = BitVec.ofNat 64 xl → S.regs 6 = BitVec.ofNat 64 xc →
    S.regs 7 = BitVec.ofNat 64 n → S.regs 10 = BitVec.ofNat 64 (k0 s xp xl n) →
    MemFrame s.mem S.mem (winA s (K kc) A) → S.mem.regions = s.mem.regions → Fw0 s S.mem →
    S.mem.readLE (s.sp.toNat + 8) 8 = zp → S.mem.readLE (s.sp.toNat + 40) 8 = xp →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

theorem inv_win {R : RtInv} {b g : Nat} {L : List (Nat × Nat)} {s : State} {kc : Nat} {M : Memory}
    (hal : K kc ≤ s.sp.toNat) (hout : Outside (s.sp.toNat - K kc) (K kc + A) R.rt) (hF : MemFrame s.mem M (winA s (K kc) A))
    (h : R.inv b L g (view R.rt L s.mem)) : R.inv b L g (view R.rt L M) := by
  refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) h
  simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [K, A] at hal hout
  rcases hr with rfl | rfl <;> (dsimp only; simp only [K, A]; exact hout.of_sub (by omega) (by omega))

end FvModexp.Arm64.ModInv
