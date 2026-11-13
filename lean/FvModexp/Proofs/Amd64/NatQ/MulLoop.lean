import FvModexp.Proofs.Amd64.NatQ.MulLoopCall
import FvModexp.Proofs.Amd64.NatQ.MulLoopAdd

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoop.lean — TIGHT COSTS] `nat.mul` (amd64): the chunk loop (natmul.go:56-59)

`lloop`: induction on the remaining chunks `m - (k + 1)·n`; each round `lcall` (the chunk product) then `ladd`
(`addTo`, back to the head); at `m ≤ (k + 1)·n` the continuation `hend` (the exit).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

/-- **the chunk loop** -/
theorem lloop (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} (hμ : μl xl yl + 3 ≤ n0)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ret : W64} {Q : State → Prop}
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
      refine lcall impl R n0 ih hμ hx150 hdf0 S hH hlt fun Lk' bk' tp' tl' tc' S' hM => ?_
      refine ladd impl hap R hmv hx150 hdf0 S' hM fun Lk'' bk'' S'' hH' => ?_
      refine ihd Lk'' bk'' (k + 1) tp' tl' tc' S'' ?_ hH'
      rw [Nat.add_mul (k + 1) 1 yl, Nat.one_mul]; omega
    · exact hend Lk bk k tp tl tc S hH hge

end FvModexp.Amd64.Q.NatMul
