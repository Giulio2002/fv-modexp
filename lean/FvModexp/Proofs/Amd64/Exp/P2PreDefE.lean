import FvModexp.Proofs.Amd64.Exp.P2PreE
import FvModexp.Proofs.Amd64.Exp.P2PreE1
import FvModexp.Proofs.Amd64.Exp.P2PreF
import FvModexp.Proofs.Amd64.Exp.P2PreX
import FvModexp.Proofs.Amd64.Exp.P2PreX1
import FvModexp.Proofs.Amd64.Exp.P2PreXT
import FvModexp.Proofs.Amd64.Exp.P2PreRnd

set_option autoImplicit false

/-! `P2Pre.PreE` (moved out of `P2Pre` by top s53 so that the Janus v0.4.0 `hinv` lemmas `P2PreInv*` can import it). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)


/-- **the precondition** (effective budget `b`): `Pre` without the call-setup facts -/
@[reducible] def PreE (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat)) (st pw pl ws lm x xl : Nat) (s : State) :
    Prop :=
  CallEnv R L s (K kc) A ∧ Serves R ∧ Globals R s.mem (win s (K kc) A ++ [(pw, pw + 24 * pl), (st, st + 24)]) ∧
    (ws = 2 ∨ ws = 4) ∧ pl = 2 ^ ws ∧ 2 ≤ lm ∧ lm ≤ 2 ^ 13 ∧
    pw % 8 = 0 ∧ pw + 24 * pl ≤ 2 ^ 48 ∧ s.mem.accessible pw (24 * pl) true = true ∧ Outside pw (24 * pl) R.rt ∧
    Outside pw (24 * pl) (win s (K kc) A) ∧ Apart pw (24 * pl) (guard s) 8 ∧ Apart pw (24 * pl) (tls s) 8 ∧
    StkSep s.mem st pw (24 * pl) ∧ (0 < xl → Apart pw (24 * pl) x (8 * xl)) ∧
    RdIn R L s (K kc) A x xl ∧ NatNorm s.mem x xl ∧ xl ≤ 2 ^ 12 ∧ (0 < xl → StkSep s.mem st x (8 * xl)) ∧
    StkPre R L s (K kc) A st ∧ stLen s.mem st + 2 ^ 12 ≤ 2 ^ 16 ∧
    (∃ op, NatOne R L s.mem op (win s (K kc) A ++ LW s pw pl st) ∧ StkSep s.mem st op 8) ∧
    cost pl lm ≤ b ∧ R.inv (b + stkR (HP (stLen s.mem st) pl lm) s.mem st) L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Outside NatAdd.wordT 16 R.rt ∧ s.mem.accessible Callees.adxAddr 1 false = true

theorem pre_of {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}
    (h : PreE R kc b L st pw pl ws lm x xl s) (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hx : s.xmm 15 = 0) (hd : s.df = false) : Pre R kc b L st pw pl ws lm x xl s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, hr, hx, hd⟩


end FvModexp.Amd64.P2Pre
