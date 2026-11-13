import FvModexp.Proofs.Arm64.NatQ.MulLoopCall
import FvModexp.Proofs.Arm64.NatQ.MulLoopAdd

/-!
# [Q-form copy of Arm64/Nat/MulLoop.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), chunk loop: induction over the chunks

`lloop`: from the head relation `LH` (any number of chunks done), given the exit (`hend`: `m ≤ i` at the head ⟹ the
goal), every run reaches the goal — the step is `lcall` (chunk product) then `ladd` (`addTo`), by induction on `m - i`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

/-- **the chunk loop** -/
theorem lloop (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} (hμ : μl xl yl + 3 ≤ n0)
    {ret : BitVec 64} {Q : State → Prop}
    (hend : ∀ (Lk : List (Nat × Nat)) (bk k tp tl tc : Nat) (S : State),
      LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S → xl ≤ (k + 1) * yl →
      ReachesRet (LibMul.program.link impl) ret S Q) :
    ∀ (d : Nat) (Lk : List (Nat × Nat)) (bk k tp tl tc : Nat) (S : State), xl - (k + 1) * yl ≤ d →
      LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S →
      ReachesRet (LibMul.program.link impl) ret S Q := by
  intro d
  induction d with
  | zero =>
    intro Lk bk k tp tl tc S hd hH
    exact hend Lk bk k tp tl tc S hH (by omega)
  | succ d ihd =>
    intro Lk bk k tp tl tc S hd hH
    rcases Nat.lt_or_ge ((k + 1) * yl) xl with hlt | hge
    · have h40 := hH.lb.h40
      refine lcall impl R n0 ih hμ S hH hlt fun Lk' bk' tp' tl' tc' S' hM => ?_
      refine ladd impl hap R hmv S' hM fun Lk'' bk'' S'' hH' => ?_
      refine ihd Lk'' bk'' (k + 1) tp' tl' tc' S'' ?_ hH'
      rw [Nat.add_mul (k + 1) 1 yl, Nat.one_mul]; omega
    · exact hend Lk bk k tp tl tc S hH hge

end FvModexp.Arm64.Q.NatMul
