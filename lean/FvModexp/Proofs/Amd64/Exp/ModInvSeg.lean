import FvModexp.Proofs.Amd64.Exp.ModInvNewton

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the join-point statements (agent infra s53; twin of `Arm64/Exp/ModInvSeg`)

The function is a chain of segment lemmas over the entry state `s` (precondition `Pre`), each ending in the statement
of the next join as a hypothesis, so the segment modules compile in parallel:
* entry → the Newton loop → `JS` (`+0x71`, `n ≤ 64`; the `CMPQ R10, $0x40` there is included, since the mask's
  `SBBQ` reads its carry) or `J0` (`+0x7b`, `n > 64`);
* `JS` → return: `k0 &= 1<<n - 1; return z.setWord(k0)`.

Frame: `PUSHQ BP` (saved `RBP` at `RSP - 8`), `SUBQ $0xd8, SP` (`RSP' = RSP - 224`, `RBP' = RSP - 8`); the return address
stays at `[RSP]`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

/-- what the function promises, from a state `S` inside its frame (entry state `s`) -/
@[reducible] def Goal (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat)
    (mulC : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (zp zc st xp xl n : Nat) (s S : State) : Prop :=
  ReachesRet (LibW.program.link impl) (retAddrOf s) S (fun s' =>
    (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
      Post R kc H sqrC mulC b L zp zc st xp xl n s s')

/-- the return address and the saved `RBP` -/
@[reducible] def Fw0 (s : State) (M : Memory) : Prop :=
  M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧ M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat

/-- the ABIInternal state facts every segment carries (`g`, TLS base, `X15`, `DF`) -/
@[reducible] def Abi (s S : State) : Prop :=
  S.regs 14 = s.regs 14 ∧ S.fsBase = s.fsBase ∧ S.xmm 15 = s.xmm 15 ∧ S.df = s.df

/-- `k0` after the Newton loop (nat.go:1293-1300) -/
@[reducible] def k0 (s : State) (xp xl n : Nat) : Nat := Exp.newton (min 64 n) (natVal s.mem xp xl % Exp.B)

/-- the state at `+0x71` / `+0x7b`: frame set up, the arguments in `RAX, RCX` (z), `RDI` (stk), `RSI, R8, R9` (x),
`R10` (n), `R12 = k0`; only the frame's stack slots written -/
@[reducible] def AtN (kc : Nat) (s S : State) (zp zc st xp xl xc n : Nat) : Prop :=
  S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) ∧ S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) ∧
    Abi s S ∧ S.regs 0 = BitVec.ofNat 64 zp ∧ S.regs 1 = BitVec.ofNat 64 zc ∧ S.regs 7 = BitVec.ofNat 64 st ∧
    S.regs 6 = BitVec.ofNat 64 xp ∧ S.regs 8 = BitVec.ofNat 64 xl ∧ S.regs 9 = BitVec.ofNat 64 xc ∧
    S.regs 10 = BitVec.ofNat 64 n ∧ S.regs 12 = BitVec.ofNat 64 (k0 s xp xl n) ∧
    MemFrame s.mem S.mem (win s (K kc) A) ∧ S.mem.regions = s.mem.regions ∧ Fw0 s S.mem ∧
    S.mem.readLE ((s.regs 4).toNat + 8) 8 = zp ∧ S.mem.readLE ((s.regs 4).toNat + 40) 8 = xp

/-- **JS** (`+0x71`, the Newton loop's exit, `n ≤ 64`) -/
def JS (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ S : State, Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s → n ≤ 64 →
    S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x71) → AtN kc s S zp zc st xp xl xc n →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- **J0** (`+0x7b`, `n > 64`) -/
def J0 (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ S : State, Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n →
    S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x7b) → AtN kc s S zp zc st xp xl xc n →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

theorem x0_eq (m : Memory) (xp xl : Nat) (hxl : 0 < xl) : m.readLE xp 8 = natVal m xp xl % Exp.B := by
  have := Exp.natVal_prefix m xp 1 xl hxl
  rw [Nat.pow_one] at this
  rw [← this]

end FvModexp.Amd64.ModInv
