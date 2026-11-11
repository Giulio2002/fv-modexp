import FvModexp.Proofs.Arm64.Top.RunDefs

/-!
# `Run` (arm64): the facts at the segment boundaries of the header phase

`RelH R b L c p len cp s ret k Lk bk S`: at a boundary after `k` length headers, the state `S` relative to the call state
`s`: Run's frame (`SP' = SP - 624`, `X29 = SP - 632`, the saved `X29`/`X30`, the four spilled arguments), the read-only
data, the input and receiver bytes unchanged, the runtime (`Lk`, `bk`), the frames, and the header `nat`s read so far
(`A`, `B`, `C` at `SP - 32`, `SP - 64`, `SP - 96`): value = EthLib's padded read of the length field, normalised, array
held in `Lk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- Where header `i`'s `nat` (`abs` of the stack `big.Int`) lives. -/
@[reducible] def hdrAt (s : State) (i : Nat) : Nat := s.sp.toNat - 32 - 32 * i

/-- Header `i` of the call data `(p, len)`: EthLib's `readNat data (32 i) 32`, as `padBE`. -/
@[reducible] def hdrV (s : State) (p len : BitVec 64) (i : Nat) : Nat := padBE s.mem p.toNat len.toNat (32 * i) 32

/-- Header `i` is read into the frame: value, normal form, and its array is a live object of `Lk`. -/
def HdrDone (m : Memory) (s : State) (p len : BitVec 64) (Lk : List (Nat × Nat)) (i : Nat) : Prop :=
  HdrOK m (hdrAt s i) (hdrV s p len i) ∧
    (0 < m.readLE (hdrAt s i + 16) 8 → InRanges (m.readLE (hdrAt s i) 8) (8 * m.readLE (hdrAt s i + 16) 8) Lk)

def RelH (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret k : Nat)
    (Lk : List (Nat × Nat)) (bk : Nat) (S : State) : Prop :=
  S.sp = s.sp - 624#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 632#64 ∧ S.regs 18 = s.regs 18 ∧
  S.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ S.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ S.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ S.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  (1 ≤ k → S.mem.readLE (s.sp.toNat - 488) 8 = min len.toNat 32 ∧
    S.mem.readLE (s.sp.toNat - 496) 8 = min len.toNat 32 + 32) ∧
  Extracted.program.DataLoaded S.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → S.mem.readLE a n = s.mem.readLE a n) ∧
  S.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - k * makeCost 4 ≤ bk ∧ R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem) ∧
  LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem S.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem S.mem L [] ∧
  (∀ i, i < k → HdrDone S.mem s p len Lk i)

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The call-data and receiver part of Run's precondition (both ISAs share its shape). -/
def InputOK (R : RtInv) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) : Prop :=
  s.mem.accessible c.toNat 3 false = true ∧ c.toNat + 3 ≤ 2 ^ 48 ∧ Held R L c.toNat 3 ∧
    Outside c.toNat 3 (win s stk 40) ∧
    p.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat ≤ cp.toNat ∧ cp.toNat < 2 ^ 48 ∧
    s.mem.accessible p.toNat len.toNat false = true ∧ Held R L p.toNat len.toNat ∧
    Outside p.toNat len.toNat (win s stk 40)

/-- The requests of the header phase (three `nat.make(4)` of the std `math/big` copy; small copies when the input is
shorter than the 96 header bytes). -/
def HdrOkR (R : RtInv) (b : Nat) (len : BitVec 64) : Prop :=
  R.ok (cA "runtime.makeslice") [SetBytesStd.wordT, 4, makeCap 4] ∧ 3 * makeCost 4 ≤ b ∧
    (len.toNat < 96 → ∀ d sr n, n ≤ 32 → R.ok (cA "runtime.memmove") [d, sr, n])

abbrev pcB1 : Nat := segAddr Extracted.program fn + 0xe4
abbrev pcB2 : Nat := segAddr Extracted.program fn + 0x19c
abbrev pcB3 : Nat := segAddr Extracted.program fn + 0x25c

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- `RelH` from its independent parts: the input and receiver bytes follow from the frames (they are held and outside the
window). -/
theorem RelH.mk' {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c p len cp : BitVec 64} {s : State} {ret k : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S : State}
    (hin : InputOK R L c p len cp s)
    (h1 : S.sp = s.sp - 624#64) (h2 : S.regs 28 = s.regs 28) (h3 : S.regs 29 = s.sp - 632#64)
    (h4 : S.regs 18 = s.regs 18)
    (h5 : S.mem.readLE (s.sp.toNat - 624) 8 = ret) (h6 : S.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat)
    (h7 : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (h8 : S.mem.readLE (s.sp.toNat + 16) 8 = p.toNat)
    (h9 : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (h10 : S.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat)
    (h11 : 1 ≤ k → S.mem.readLE (s.sp.toNat - 488) 8 = min len.toNat 32 ∧
      S.mem.readLE (s.sp.toNat - 496) 8 = min len.toNat 32 + 32)
    (h12 : Extracted.program.DataLoaded S.mem)
    (h15 : LiveExt R L Lk) (h16 : b - k * makeCost 4 ≤ bk)
    (h17 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) (h18 : LiveSep Lk (win s stk 40))
    (h19 : MemFrame s.mem S.mem (R.rt ++ winA s stk 40)) (h20 : LiveFrame s.mem S.mem L [])
    (h21 : ∀ i, i < k → HdrDone S.mem s p len Lk i) :
    RelH R b L c p len cp s ret k Lk bk S := by
  obtain ⟨-, -, hch, hcw, -, -, -, -, hh, hpw⟩ := hin
  have hLw := LiveFrame.of_nil' h20 (winA s stk 40)
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun a n ha hb => ?_, ?_, h15, h16, h17, h18, h19, h20, h21⟩
  · refine (hh.sub ha hb).readLE h19 hLw ?_
    simp only [win, winA, Janus.outside_cons, Janus.outside_nil, and_true] at hpw ⊢
    omega
  · refine hch.readLE h19 hLw ?_
    simp only [win, winA, Janus.outside_cons, Janus.outside_nil, and_true] at hcw ⊢
    omega

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- Big-endian reads agree where single bytes do. -/
theorem beVal_of_reads {m m' : Memory} {a n : Nat} (h : ∀ i, i < n → m'.readLE (a + i) 1 = m.readLE (a + i) 1) :
    beVal m' a n = beVal m a n :=
  beVal_congr fun i hi => by
    have := h i hi; simp only [Memory.readLE_one] at this; exact BitVec.eq_of_toNat_eq this

/-- A header read by `setBytes` and stored into the frame: `HdrDone` from the callee's post (memory `m`) and the frame
stores (memory `M`, equal to `m` outside Run's window). -/
theorem hdrDone_of {R : RtInv} {L1 : List (Nat × Nat)} {m M : Memory} {s : State} {p len : BitVec 64} {i p1 n1 c1 : Nat}
    (hrd : ∀ a n, Outside a n (win s stk 40) → M.readLE a n = m.readLE a n)
    (hs0 : M.readLE (hdrAt s i) 8 = p1) (hs1 : M.readLE (hdrAt s i + 8) 8 = n1)
    (hs2 : M.readLE (hdrAt s i + 16) 8 = c1)
    (hv : natVal m p1 n1 = hdrV s p len i) (hn : NatNorm m p1 n1) (hn4 : n1 ≤ 4) (hnc : n1 ≤ c1)
    (hfresh : 0 < c1 → InRanges p1 (8 * c1) R.rt) (hlive : NatLive m R L1 p1 c1)
    (hout : Outside (s.sp.toNat - stk) (stk + 40) R.rt) : HdrDone M s p len L1 i := by
  have hw : 0 < c1 → Outside p1 (8 * c1) (win s stk 40) := fun hc => by
    have := InRanges.apart (hfresh hc) hout
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; unfold Apart at this; omega
  have hval : natVal M p1 n1 = natVal m p1 n1 := by
    by_cases h0 : n1 = 0
    · subst h0; rfl
    · exact hrd _ _ ((hw (by omega)).of_sub (Nat.le_refl _) (by omega))
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [natAt, hdrAt] at *; rw [show s.sp.toNat - 32 - 32 * i + 8 = s.sp.toNat - 32 - 32 * i + 8 from rfl]
    rw [hs0, hs1, hval, hv]
  · simp only [hdrAt] at *; rw [hs0, hs1]
    by_cases h0 : n1 = 0
    · exact Or.inl h0
    · rcases hn with h | h
      · exact Or.inl h
      · right
        rw [hrd _ _ ((hw (by omega)).of_sub (by omega) (by omega))]; exact h
  · simp only [hdrAt] at *; rw [hs1]; exact hn4
  · simp only [hdrAt] at *; rw [hs0, hs2]
    intro hc
    exact ((hlive hc).2.1).inRanges_of_rt (hfresh hc) (by omega)

end FvModexp.Arm64.Run
