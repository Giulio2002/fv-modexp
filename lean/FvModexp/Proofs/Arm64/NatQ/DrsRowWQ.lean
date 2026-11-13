import FvModexp.Proofs.Arm64.Nat.DrsRowW
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# Row `DrsRowQ` (arm64): the witness precondition in the Q-form (TIGHT COSTS, asm s39)

The witness of `DrsRow` (Nat/DrsRowW.lean: `u = [1, 0, 0]`, `v = [0, 2^63]`, `q = [0]`, the stack `{w, 0, 4}`, budget
`0x80000`) at the reserve level `H = 88` (`= stLen + 12·len v + 64`); the level-free cost `drsCQ 3 2 = 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.DrsRow.Witness

open FvModexp.Arm64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

theorem cost0Q : Q.drsCQ 3 2 + stkR 88 mem0 ST ≤ 0x80000 := by
  rw [Q.drsCQ_small (by decide)]; decide +kernel

theorem preQ : Q.DivLarge.DrsPre R 0x80000 [] 88 (Q.drsCQ 3 2) OA 1 1 ST OB 3 3 VP 2 2 s0 := by
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.sp = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 28 = BitVec.ofNat 64 G0 := rfl
  simp only [Q.DivLarge.DrsPre, Q.DivLarge.DrsPreW, CallEnv, Globals, EvenHyp.StkIn, ExpHyp.StackOK', StkOK, hm, hsp, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ⟨by decide +kernel, cost0Q⟩, inv1 _⟩
  all_goals try and_intros
  all_goals first
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | (intro r hr; simp at hr; done)
    | (intros; trivial)
    | (intro p c hpc hc; rcases hpc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> exact absurd hc (by omega))
    | (intro _; and_intros <;> first
        | (simp only [acc0] <;> decide +kernel)
        | exact Or.inr (rtOut _ _ (by decide +kernel))
        | (simp only [win, stW, stCap, outside_cons, outside_nil, and_true] <;> decide +kernel)
        | (unfold Apart <;> decide +kernel)
        | decide +kernel)
    | (simp only [NatLive]; intro h; exact absurd h (by decide))
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (show _ = _; decide)
    | (exact Or.inr (rtOut _ _ (by decide +kernel)))
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)),
        by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (intro h; exact absurd h (by decide))
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (intro _; exact ⟨by unfold Apart; decide +kernel, by unfold Apart; decide +kernel⟩)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | (simp only [natVal] <;> decide +kernel)
    | (simp only [Held, InRanges] <;> exact Or.inr (rtOut _ _ (by decide +kernel)))
    | decide +kernel

end FvModexp.Arm64.DrsRow.Witness
