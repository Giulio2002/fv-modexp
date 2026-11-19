import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# Frame lemmas for installing the return address (amd64, Janus v0.4.0 `hinv`; top s54)

Since Janus v0.4.0 a precondition is evaluated before the return address is written at `[RSP]` (`State.setRet`), and
`Ensures.of_old` needs `pre s → pre (s.setRet ret)`. `setRet` writes only `[RSP, RSP + 8)`, which lies inside the call
window `win s stk above = [RSP - stk, RSP + above)` whenever `8 ≤ above`. So every read the precondition places outside
the window is unchanged (`rd`), and the window-level facts carry over (`callEnv`, `natLive`, `natNorm`). These are used
to prove `hinv` by hand where `janus64_pre_setRet`'s closer is too slow or cannot see an apartness fact (it is behind
a guard such as `0 < n →` or under an `∃`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.SetRetWin

/-- a read outside the call window `[RSP - stk, RSP + above)` (`8 ≤ above`) misses the return slot -/
theorem rd {s : State} {ret stk above a n : Nat} (hab : 8 ≤ above) (h : Outside a n (win s stk above)) :
    (s.setRet ret).mem.readLE a n = s.mem.readLE a n := by
  apply readLE_setRet_of_disjoint
  simp only [win, outside_cons, outside_nil, and_true] at h
  omega

theorem natLive {s : State} {ret : Nat} {R : RtInv} {L : List (Nat × Nat)} {p c : Nat} :
    NatLive (s.setRet ret).mem R L p c ↔ NatLive s.mem R L p c := by
  simp only [NatLive, setRet_accessible]

theorem callEnv {R : RtInv} {L : List (Nat × Nat)} {s : State} {ret stk above : Nat} (hab : 8 ≤ above)
    (h : CallEnv R L s stk above) : CallEnv R L (s.setRet ret) stk above := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨a1, a2, a3⟩ := h2
  simp only [regSP] at a1 a2 a3
  have hacc : s.mem.accessible (s.regs 4).toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ a3 (by omega) (by omega)
  obtain ⟨t1, t2, t3⟩ := h10
  have ht : s.fsBase.toNat ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 16 ≤ s.fsBase.toNat := by
    simp only [Apart] at t3; omega
  exact ⟨stackGuardOK_setRet.2 h1, ⟨a1, a2, by rw [setRet_accessible]; exact a3⟩, h3, (dataLoaded_setRet_iff hacc).2 h4,
    h5, h6, h7, h8, h9, ⟨(tlsG_setRet_iff ht).2 t1, t2, t3⟩⟩

/-- `NatNorm` of an operand that is empty or outside the window -/
theorem natNorm {s : State} {ret stk above p n : Nat} (hab : 8 ≤ above)
    (h : n = 0 ∨ Outside p (8 * n) (win s stk above)) (hn : NatNorm s.mem p n) : NatNorm (s.setRet ret).mem p n := by
  rw [natNorm_setRet]
  · exact hn
  rcases h with h | h
  · exact Or.inl h
  · simp only [win, outside_cons, outside_nil, and_true] at h
    omega

/-- the frame step for a range `[lo, hi)` containing the return slot -/
theorem rdR {s : State} {ret lo hi a n : Nat} (hlo : lo ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ hi)
    (h : a + n ≤ lo ∨ hi ≤ a) : (s.setRet ret).mem.readLE a n = s.mem.readLE a n :=
  readLE_setRet_of_disjoint (by omega)

/-- `rdR` for an `Apart` fact against the range `[lo, lo + k)` -/
theorem rdA {s : State} {ret lo k a n : Nat} (hlo : lo ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ lo + k)
    (h : Apart a n lo k) : (s.setRet ret).mem.readLE a n = s.mem.readLE a n :=
  rdR hlo hhi (by unfold Apart at h; omega)

/-- `rdR` for an `Outside` fact over a window list whose first range contains the slot -/
theorem rdO {s : State} {ret lo hi a n : Nat} {rest : List (Nat × Nat)} (hlo : lo ≤ (s.regs 4).toNat)
    (hhi : (s.regs 4).toNat + 8 ≤ hi) (h : Outside a n ((lo, hi) :: rest)) :
    (s.setRet ret).mem.readLE a n = s.mem.readLE a n :=
  rdR hlo hhi h.1

/-- `NatNorm` of an operand that is empty or apart from a range containing the slot -/
theorem natNormA {s : State} {ret lo k p n : Nat} (hlo : lo ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ lo + k)
    (h : Apart p (8 * n) lo k) (hn : NatNorm s.mem p n) : NatNorm (s.setRet ret).mem p n := by
  rw [natNorm_setRet]
  · exact hn
  unfold Apart at h
  omega

/-- `RSP = sp + c` written as `regs 4 = ofNat (RSP - c + c)` forces `c ≤ RSP` -/
theorem le_of_regs_eq {x : BitVec 64} {c : Nat} (hc : c < 2 ^ 64) (e : x = BitVec.ofNat 64 (x.toNat - c + c)) :
    c ≤ x.toNat := by
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- a stack word at `RSP - c + k` with `c + 8 ≤ k` (above the return slot) survives -/
theorem stackArg {s : State} {ret c k v : Nat} (hR : c ≤ (s.regs 4).toNat) (hk : c + 8 ≤ k)
    (h : s.mem.readLE ((s.regs 4).toNat - c + k) 8 = v) : (s.setRet ret).mem.readLE ((s.regs 4).toNat - c + k) 8 = v :=
  (readLE_setRet_of_disjoint (Or.inr (by omega))).trans h

theorem apart_mono {a n m b k : Nat} (h : Apart a n b k) (hm : m ≤ n) : Apart a m b k := by
  unfold Apart at h ⊢; omega

theorem slot_hi {r c d : Nat} (hc : c ≤ r) (hd : c + 8 ≤ d) : r + 8 ≤ r - c + d := by omega

theorem slot_hiK {r c d K : Nat} (hc : c ≤ r) (hK : K ≤ r - c) (hd : c + 8 ≤ d) : r + 8 ≤ r - c - K + (K + d) := by omega

end FvModexp.Amd64.SetRetWin
