import FvModexp.Proofs.Arm64.Nat.SqrMulX

/-!
# `ResSep` for the `nat.sqr` / `nat.mul` export posts (arm64; owner divmc)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

/-! ## `ResSep` (coordinator decision on "[expmc s26] ResSep") — derived from the posts' apartness clause

The posts state "fresh result ⇒ apart from the stack's final array"; a reused result (`z` itself) is held at entry,
so it is apart from a final array that is not the entry one (`StackBack`: such an array is fresh wrt `L`). -/

theorem resSep_of_fa {R : RtInv} {L L' : List (Nat × Nat)} {st zp zc p c : Nat} {m0 m : Memory}
    (hz : 0 < zc → Held R L zp (8 * zc)) (hsb : StackBackL R L L' st m0 m)
    (hfa : ¬ (p = zp ∧ c = zc) → 0 < c → 0 < stCap m st → Apart p (8 * c) (stW m st) (8 * stCap m st)) :
    ResSep m0 m st p c := by
  intro hc hn
  by_cases hk : p = zp ∧ c = zc
  · obtain ⟨rfl, rfl⟩ := hk
    exact ResSep.of_held hsb.1.2.2 (hz hc) hc hn
  · exact hfa hk hc (hsb.2 hn).2

/-- `nat.sqr`'s post gives `ResSep` for its result (given `z` held at entry, as `SqrPre`'s `NatLive` says) -/
theorem SqrPostL.resSep {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {stk above zp zc st x xl : Nat}
    {s s' : State} (hz : 0 < zc → Held R L zp (8 * zc)) (h : SqrPostL R b c L stk above zp zc st x xl s s') :
    ∃ p' c' : Nat, s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧ ResSep s.mem s'.mem st p' c' := by
  obtain ⟨p', l', c', h0, -, h2, L', b', -, -, hsb, hfa, -⟩ := h
  exact ⟨p', c', h0, h2, resSep_of_fa hz hsb hfa⟩

/-- `nat.mul`'s post gives `ResSep` for its result (given `z` held at entry) -/
theorem MulPostL.resSep {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {stk above zp zc st x xl y yl : Nat}
    {s s' : State} (hz : 0 < zc → Held R L zp (8 * zc)) (h : MulPostL R b c L stk above zp zc st x xl y yl s s') :
    ∃ p' c' : Nat, s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧ ResSep s.mem s'.mem st p' c' := by
  obtain ⟨p', l', c', h0, -, h2, L', b', -, -, hsb, hfa, -⟩ := h
  exact ⟨p', c', h0, h2, resSep_of_fa hz hsb hfa⟩

end FvModexp.Arm64.EvenHyp
