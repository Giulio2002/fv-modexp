import FvModexp.Proofs.Arm64.Top.RunRel

/-!
# `Run` (arm64): the operand phase (`C0` to `C1`): relations

After the length checks `Run` reads the three operands (`getData(input[96:], start, size)` padded by `RightPadBytes`,
then the patched `nat.setBytes`) into the stack `big.Int`s `base` (`SP - 136`), `exp` (`SP - 168`), `mod` (`SP - 200`):
`neg` byte, then `abs = (ptr, len, cap)`. `RelD … k …` holds between the operand segments (`k` operands read).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- The `big.Int` of operand `j` (0 base, 1 exp, 2 mod): its `neg` byte; `abs` is at `+ 8`. -/
@[reducible] def opAt (s : State) (j : Nat) : Nat := s.sp.toNat - 136 - 32 * j

/-- Where operand `j` starts in the call data (after the 96 header bytes) and its length. -/
@[reducible] def opStart (s : State) (p len : BitVec 64) (j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then hdrV s p len 0 else hdrV s p len 0 + hdrV s p len 1
@[reducible] def opLen (s : State) (p len : BitVec 64) (j : Nat) : Nat :=
  if j = 0 then hdrV s p len 0 else if j = 1 then hdrV s p len 1 else hdrV s p len 2

/-- Operand `j`'s value: EthLib's `readNat data (96 + start) size`, as `padBE`. -/
@[reducible] def opV (s : State) (p len : BitVec 64) (j : Nat) : Nat :=
  padBE s.mem p.toNat len.toNat (96 + opStart s p len j) (opLen s p len j)

/-- Operand `j` is read: `neg = 0`, the value, normal form, at most 128 limbs, `len ≤ cap`, the array a live object of
`Lk`, aligned, accessible, below `2^48`. -/
def OpDone (m : Memory) (s : State) (p len : BitVec 64) (Lk : List (Nat × Nat)) (j : Nat) : Prop :=
  m.readLE (opAt s j) 1 = 0 ∧ natAt m (opAt s j + 8) = opV s p len j ∧
    NatNorm m (m.readLE (opAt s j + 8) 8) (m.readLE (opAt s j + 16) 8) ∧ m.readLE (opAt s j + 16) 8 ≤ 128 ∧
    m.readLE (opAt s j + 16) 8 ≤ m.readLE (opAt s j + 24) 8 ∧
    (0 < m.readLE (opAt s j + 24) 8 →
      InRanges (m.readLE (opAt s j + 8) 8) (8 * m.readLE (opAt s j + 24) 8) Lk ∧
      m.readLE (opAt s j + 8) 8 % 8 = 0 ∧
      s.mem.accessible (m.readLE (opAt s j + 8) 8) (8 * m.readLE (opAt s j + 24) 8) true = true ∧
      m.readLE (opAt s j + 8) 8 + 8 * m.readLE (opAt s j + 24) 8 ≤ 2 ^ 48)

/-- The budget one operand may use: the `RightPadBytes` buffer (at most 1024 bytes) and the `nat.make` of `setBytes`
(at most 128 words). -/
def dCost : Nat := allocCost 1024 + allocCost (8 * 132)

/-- The input slice after the 96 header bytes: `input[96:]` (`(p + 96, len - 96, cp - 96)`), or empty at `p`. -/
@[reducible] def inOff (len : BitVec 64) : Nat := if 96 < len.toNat then 96 else 0

def RelD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret k : Nat)
    (Lk : List (Nat × Nat)) (bk : Nat) (S : State) : Prop :=
  S.sp = s.sp - 624#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 632#64 ∧ S.regs 18 = s.regs 18 ∧
  S.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ S.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ S.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ S.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  S.mem.readLE (s.sp.toNat - 520) 8 = hdrV s p len 0 ∧ S.mem.readLE (s.sp.toNat - 528) 8 = hdrV s p len 1 ∧
  S.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ S.mem.readLE (s.sp.toNat - 480) 8 = len.toNat - 96 ∧
  S.mem.readLE (s.sp.toNat - 472) 8 = cp.toNat - inOff len ∧ S.mem.readLE (s.sp.toNat - 216) 8 = p.toNat + inOff len ∧
  hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024 ∧ ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) ∧
  (1 ≤ k → S.mem.readLE (s.sp.toNat - 504) 8 = min (hdrV s p len 0) (len.toNat - 96) ∧
    S.mem.readLE (s.sp.toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1) ∧
  Extracted.program.DataLoaded S.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → S.mem.readLE a n = s.mem.readLE a n) ∧
  S.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + k * dCost) ≤ bk ∧ R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem) ∧
  LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem S.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem S.mem L [] ∧
  (∀ j, j < k → OpDone S.mem s p len Lk j)

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

theorem RelD.mk' {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c p len cp : BitVec 64} {s : State} {ret k : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S : State}
    (hin : InputOK R L c p len cp s)
    (h1 : S.sp = s.sp - 624#64) (h2 : S.regs 28 = s.regs 28) (h3 : S.regs 29 = s.sp - 632#64)
    (h4 : S.regs 18 = s.regs 18)
    (h5 : S.mem.readLE (s.sp.toNat - 624) 8 = ret) (h6 : S.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat)
    (h7 : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (h8 : S.mem.readLE (s.sp.toNat + 16) 8 = p.toNat)
    (h9 : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (h10 : S.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat)
    (s1 : S.mem.readLE (s.sp.toNat - 520) 8 = hdrV s p len 0) (s2 : S.mem.readLE (s.sp.toNat - 528) 8 = hdrV s p len 1)
    (s3 : S.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2) (s4 : S.mem.readLE (s.sp.toNat - 480) 8 = len.toNat - 96)
    (s5 : S.mem.readLE (s.sp.toNat - 472) 8 = cp.toNat - inOff len)
    (s6 : S.mem.readLE (s.sp.toNat - 216) 8 = p.toNat + inOff len)
    (l0 : hdrV s p len 0 ≤ 1024) (l1 : hdrV s p len 1 ≤ 1024) (l2 : hdrV s p len 2 ≤ 1024)
    (lnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (k1 : 1 ≤ k → S.mem.readLE (s.sp.toNat - 504) 8 = min (hdrV s p len 0) (len.toNat - 96) ∧
      S.mem.readLE (s.sp.toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1)
    (h12 : Extracted.program.DataLoaded S.mem)
    (h15 : LiveExt R L Lk) (h16 : b - (3 * makeCost 4 + k * dCost) ≤ bk)
    (h17 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) (h18 : LiveSep Lk (win s stk 40))
    (h19 : MemFrame s.mem S.mem (R.rt ++ winA s stk 40)) (h20 : LiveFrame s.mem S.mem L [])
    (h21 : ∀ j, j < k → OpDone S.mem s p len Lk j) :
    RelD R b L c p len cp s ret k Lk bk S := by
  obtain ⟨-, -, hch, hcw, -, -, -, -, hh, hpw⟩ := hin
  have hLw := LiveFrame.of_nil' h20 (winA s stk 40)
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, s1, s2, s3, s4, s5, s6, l0, l1, l2, lnz, k1, h12,
    fun a n ha hb => ?_, ?_, h15, h16, h17, h18, h19, h20, h21⟩
  · refine (hh.sub ha hb).readLE h19 hLw ?_
    simp only [win, winA, Janus.outside_cons, Janus.outside_nil, and_true] at hpw ⊢
    omega
  · refine hch.readLE h19 hLw ?_
    simp only [win, winA, Janus.outside_cons, Janus.outside_nil, and_true] at hcw ⊢
    omega

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- An operand read by `setBytes` and stored into its `big.Int` (memory `M`, equal to the callee's `m` outside the window). -/
theorem opDone_of {R : RtInv} {L1 : List (Nat × Nat)} {m M : Memory} {s : State} {p len : BitVec 64} {j p1 n1 c1 : Nat}
    (hrd : ∀ a n, Outside a n (win s stk 40) → M.readLE a n = m.readLE a n)
    (hacc : ∀ a n w, m.accessible a n w = s.mem.accessible a n w)
    (hs : M.readLE (opAt s j) 1 = 0) (hs0 : M.readLE (opAt s j + 8) 8 = p1) (hs1 : M.readLE (opAt s j + 16) 8 = n1)
    (hs2 : M.readLE (opAt s j + 24) 8 = c1)
    (hv : natVal m p1 n1 = opV s p len j) (hn : NatNorm m p1 n1) (hn4 : n1 ≤ 128) (hnc : n1 ≤ c1)
    (hfresh : 0 < c1 → InRanges p1 (8 * c1) R.rt) (hlive : NatLive m R L1 p1 c1)
    (hout : Outside (s.sp.toNat - stk) (stk + 40) R.rt) : OpDone M s p len L1 j := by
  have hw : 0 < c1 → Outside p1 (8 * c1) (win s stk 40) := fun hc => by
    have := InRanges.apart (hfresh hc) hout
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; unfold Apart at this; omega
  have hval : natVal M p1 n1 = natVal m p1 n1 := by
    by_cases h0 : n1 = 0
    · subst h0; rfl
    · exact hrd _ _ ((hw (by omega)).of_sub (Nat.le_refl _) (by omega))
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [natAt]; rw [show opAt s j + 8 + 8 = opAt s j + 16 by omega, hs0, hs1, hval, hv]
  · rw [hs0, hs1]
    by_cases h0 : n1 = 0
    · exact Or.inl h0
    · rcases hn with h | h
      · exact Or.inl h
      · right
        rw [hrd _ _ ((hw (by omega)).of_sub (by omega) (by omega))]; exact h
  · rw [hs1]; exact hn4
  · rw [hs1, hs2]; exact hnc
  · rw [hs0, hs2]
    intro hc
    obtain ⟨h1, h2, h3, h4⟩ := hlive hc
    exact ⟨h2.inRanges_of_rt (hfresh hc) (by omega), h1, by rw [← hacc]; exact h3, h4⟩

/-- An operand already read stays read: its four slots unchanged, its array unchanged (a live object), the live set grows. -/
theorem OpDone.transport {m m' : Memory} {s : State} {p len : BitVec 64} {L1 L2 : List (Nat × Nat)} {j : Nat}
    (h : OpDone m s p len L1 j)
    (h0 : m'.readLE (opAt s j) 1 = m.readLE (opAt s j) 1)
    (h1 : m'.readLE (opAt s j + 8) 8 = m.readLE (opAt s j + 8) 8)
    (h2 : m'.readLE (opAt s j + 16) 8 = m.readLE (opAt s j + 16) 8)
    (h3 : m'.readLE (opAt s j + 24) 8 = m.readLE (opAt s j + 24) 8)
    (hLF : LiveFrame m m' L1 []) (hsub : ∀ a n, InRanges a n L1 → InRanges a n L2) : OpDone m' s p len L2 j := by
  obtain ⟨hneg, hv, hn, h4, hcl, hin⟩ := h
  simp only [natAt] at hv
  refine ⟨by rw [h0]; exact hneg, ?_, ?_, by rw [h2]; exact h4, by rw [h2, h3]; exact hcl, ?_⟩
  · simp only [natAt]; rw [show opAt s j + 8 + 8 = opAt s j + 16 by omega] at hv ⊢; rw [h1, h2]
    by_cases hz : m.readLE (opAt s j + 16) 8 = 0
    · rw [hz]; rw [hz] at hv; exact hv
    · rw [natVal, hLF.readLE _ _ (((hin (by omega)).1).sub (Nat.le_refl _) (by omega)) trivial]; exact hv
  · rw [h1, h2]
    rcases hn with hn | hn
    · exact Or.inl hn
    · by_cases hz : m.readLE (opAt s j + 16) 8 = 0
      · exact Or.inl hz
      · right; rw [hLF.readLE _ _ (((hin (by omega)).1).sub (by omega) (by omega)) trivial]; exact hn
  · rw [h1, h3]; intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hin hc
    exact ⟨hsub _ _ a1, a2, a3, a4⟩

end FvModexp.Arm64.Run
