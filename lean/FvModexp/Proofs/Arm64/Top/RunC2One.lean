import FvModexp.Proofs.Arm64.Top.RunC2Lem
import FvModexp.Spec.RunArm64

set_option autoImplicit false

/-! # `Run` (arm64): the `natOne` global at the `(*Int).exp` call (`RunIface.OneG`), from `Run`'s `Spec.RunArm64.NatOne`

`natOne`'s header and word lie outside the runtime-owned ranges and `Run`'s window, so `Run`'s writes (stack frame,
fresh heap objects) keep them; the operand headers lie in the window and their arrays in the runtime-owned ranges, so
both are apart from them. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem oneG_ops {R : RtInv} {L L1 : List (Nat × Nat)} {p len : BitVec 64} {s T : State} {M : Memory}
    {W stkM aboveM : Nat} (xs : List Nat)
    (hT : T.sp.toNat = s.sp.toNat - 624) (hW : 624 + stkM ≤ W) (hab : aboveM ≤ 160)
    (hsW : W ≤ s.sp.toNat) (hone : FvModexp.Spec.RunArm64.NatOne R s.mem (win s W 40))
    (hMF : MemFrame s.mem M (R.rt ++ winA s 4800 40)) (hW1 : 4800 ≤ W)
    (hop : ∀ j, j < 3 → OpDone R M s p len L L1 j)
    (hxs : ∀ a ∈ xs, ∃ j, j < 3 ∧ a = opAt s j) :
    RunIface.OneG R L1 M (win T stkM aboveM) xs := by
  dsimp only [FvModexp.Spec.RunArm64.NatOne] at hone
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» = RunIface.natOneA from rfl] at hone
  obtain ⟨h8, h16, hw1, hacc, hrt, hwin, hacco, h48, hort, howin⟩ := hone
  generalize hop0 : s.mem.readLE RunIface.natOneA 8 = op at h8 h16 hw1 hacc hrt hwin hacco h48 hort howin
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwin howin
  have hO : ∀ a n, (a + n ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ a) → Outside a n R.rt →
      Outside a n (R.rt ++ winA s 4800 40) := fun a n h1 h2 => by
    simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨h2, by omega, by omega⟩
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

/-- `stackPool`'s `New` word at the `Mod` / `exp` call (`RunIface.PoolG`), from `Run`'s `Spec.RunArm64.StackPool`: the word
lies outside the runtime-owned ranges and `Run`'s window, so `Run`'s writes keep it. -/
theorem poolG_ops {R : RtInv} {s T : State} {M : Memory} {W stkM aboveM : Nat}
    (hT : T.sp.toNat = s.sp.toNat - 624) (hW : 624 + stkM ≤ W) (hab : aboveM ≤ 160)
    (hsW : W ≤ s.sp.toNat) (hpool : FvModexp.Spec.RunArm64.StackPool R s.mem (win s W 40))
    (hMF : MemFrame s.mem M (R.rt ++ winA s 4800 40)) (hW1 : 4800 ≤ W) :
    RunIface.PoolG R M (win T stkM aboveM) := by
  dsimp only [FvModexp.Spec.RunArm64.StackPool] at hpool
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.stackPool» = RunIface.stackPoolA
    from rfl] at hpool
  obtain ⟨h0, hw, hrt, hwin⟩ := hpool
  unfold RunIface.PoolG
  generalize RunIface.stackPoolA + Pool.newOffset = a at hw hrt hwin ⊢
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwin
  refine ⟨h0, ?_, hrt, ?_⟩
  · rw [hMF.readLE _ _ (by
      simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hrt, by omega, by omega⟩)]
    exact hw
  · simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; rw [hT]; omega

end FvModexp.Arm64.Run
