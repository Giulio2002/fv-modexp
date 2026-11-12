import FvModexp.Proofs.Amd64.Top.RunC2Lem
import FvModexp.Spec.RunAmd64

set_option autoImplicit false

/-! # `Run` (amd64): the `natOne` global at the `(*Int).exp` call (`RunIface.OneG`), from `Run`'s `Spec.RunAmd64.NatOne`

As arm64 (`FvModexp.Arm64.Run.oneG_ops`); `oneG_push` moves the fact over the `CALL`'s return-address push (the pushed
slot lies in the callee's window, apart from `natOne` and from the operand headers). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem oneG_ops {R : RtInv} {L L1 : List (Nat × Nat)} {p len : BitVec 64} {s T : State} {M : Janus.Arm64.Memory}
    {W stkM aboveM : Nat} (xs : List Nat)
    (hT : (T.regs 4).toNat = (s.regs 4).toNat - 616) (hW : 616 + stkM ≤ W) (hab : aboveM ≤ 144)
    (hsW : W ≤ (s.regs 4).toNat) (hone : FvModexp.Spec.RunAmd64.NatOne R s.mem (win s W 40))
    (hMF : MemFrame s.mem M (R.rt ++ win s 4800 40)) (hW1 : 4800 ≤ W)
    (hop : ∀ j, j < 3 → OpDone R M s p len L L1 j)
    (hxs : ∀ a ∈ xs, ∃ j, j < 3 ∧ a = opAt s j) :
    RunIface.OneG R L1 M (win T stkM aboveM) xs := by
  dsimp only [FvModexp.Spec.RunAmd64.NatOne] at hone
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» = RunIface.natOneA from rfl] at hone
  obtain ⟨h8, h16, hw1, hacc, hrt, hwin, hacco, h48, hort, howin⟩ := hone
  generalize hop0 : s.mem.readLE RunIface.natOneA 8 = op at h8 h16 hw1 hacc hrt hwin hacco h48 hort howin
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwin howin
  have hO : ∀ a n, (a + n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 40 ≤ a) → Outside a n R.rt →
      Outside a n (R.rt ++ win s 4800 40) := fun a n h1 h2 => by
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨h2, by omega⟩
  have hnA : ∀ k, k + 8 ≤ 24 → M.readLE (RunIface.natOneA + k) 8 = s.mem.readLE (RunIface.natOneA + k) 8 :=
    fun k hk => hMF.readLE _ _ (hO _ _ (by omega) (hrt.of_sub (by omega) (by omega)))
  refine ⟨op, ⟨?_, ?_, ?_, ?_, by rw [hMF.accessible]; exact hacc, hrt, ?_, by rw [hMF.accessible]; exact hacco, h48,
    Or.inr hort, ?_⟩, fun a ha => ?_⟩
  · rw [show RunIface.natOneA = RunIface.natOneA + 0 by rfl, hnA 0 (by omega)]; exact hop0
  · rw [hnA 8 (by omega)]; exact h8
  · rw [hnA 16 (by omega)]; exact h16
  · rw [hMF.readLE _ _ (hO _ _ (by omega) hort)]; exact hw1
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; omega
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; omega
  · obtain ⟨j, hj, rfl⟩ := hxs a ha
    obtain ⟨-, -, -, -, -, hlive⟩ := hop j hj
    refine ⟨by unfold Apart; simp only [opAt]; omega, by unfold Apart; simp only [opAt]; omega, fun hc => ⟨?_, ?_⟩⟩
    · exact (InRanges.apart (hlive hc).2.2.2.2.1 hrt).symm
    · exact (InRanges.apart (hlive hc).2.2.2.2.1 hort).symm

/-- `OneG` survives a store of 8 bytes inside the window `[(lo, hi)]` that misses the operand headers. -/
theorem oneG_push {R : RtInv} {L : List (Nat × Nat)} {m : Janus.Arm64.Memory} {lo hi : Nat} {xs : List Nat}
    {addr v : Nat} (h : RunIface.OneG R L m [(lo, hi)] xs) (hin : lo ≤ addr ∧ addr + 8 ≤ hi)
    (hxs : ∀ a ∈ xs, a + 32 ≤ addr ∨ addr + 8 ≤ a) :
    RunIface.OneG R L (m.writeLE addr 8 v) [(lo, hi)] xs := by
  obtain ⟨op, ⟨h0, h8, h16, hw1, hacc, hrt, hwin, hacco, h48, hheld, howin⟩, hap⟩ := h
  have hwin' := hwin
  have howin' := howin
  simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hwin' howin'
  have hr : ∀ a n, (a + n ≤ addr ∨ addr + 8 ≤ a) → (m.writeLE addr 8 v).readLE a n = m.readLE a n :=
    fun a n hd => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨op, ⟨by rw [hr _ _ (by omega)]; exact h0, by rw [hr _ _ (by omega)]; exact h8,
    by rw [hr _ _ (by omega)]; exact h16, by rw [hr _ _ (by omega)]; exact hw1,
    by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc, hrt, hwin,
    by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacco, h48, hheld, howin⟩, fun a ha => ?_⟩
  have hd := hxs a ha
  rw [hr (a + 8) 8 (by omega), hr (a + 24) 8 (by omega)]
  exact hap a ha

/-- `stackPool`'s `New` word at the `Mod` / `exp` call (`RunIface.PoolG`), from `Run`'s `Spec.RunAmd64.StackPool` (as
arm64 `poolG_ops`). -/
theorem poolG_ops {R : RtInv} {s T : State} {M : Janus.Arm64.Memory} {W stkM aboveM : Nat}
    (hT : (T.regs 4).toNat = (s.regs 4).toNat - 616) (hW : 616 + stkM ≤ W) (hab : aboveM ≤ 144)
    (hsW : W ≤ (s.regs 4).toNat) (hpool : FvModexp.Spec.RunAmd64.StackPool R s.mem (win s W 40))
    (hMF : MemFrame s.mem M (R.rt ++ win s 4800 40)) (hW1 : 4800 ≤ W) :
    RunIface.PoolG R M (win T stkM aboveM) := by
  dsimp only [FvModexp.Spec.RunAmd64.StackPool] at hpool
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.stackPool» = RunIface.stackPoolA
    from rfl] at hpool
  obtain ⟨h0, hw, hrt, hwin⟩ := hpool
  unfold RunIface.PoolG
  generalize RunIface.stackPoolA + Pool.newOffset = a at hw hrt hwin ⊢
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwin
  refine ⟨h0, ?_, hrt, ?_⟩
  · rw [hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hrt, by omega⟩)]
    exact hw
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; omega

/-- `PoolG` survives a store of 8 bytes inside the window `[(lo, hi)]`. -/
theorem poolG_push {R : RtInv} {m : Janus.Arm64.Memory} {lo hi : Nat} {addr v : Nat}
    (h : RunIface.PoolG R m [(lo, hi)]) (hin : lo ≤ addr ∧ addr + 8 ≤ hi) :
    RunIface.PoolG R (m.writeLE addr 8 v) [(lo, hi)] := by
  obtain ⟨h0, hw, hrt, hwin⟩ := h
  refine ⟨h0, ?_, hrt, hwin⟩
  have hwin' := hwin
  simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hwin'
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hw

end FvModexp.Amd64.Run
