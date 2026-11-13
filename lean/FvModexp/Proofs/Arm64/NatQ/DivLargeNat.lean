import FvModexp.Proofs.Arm64.NatQ.DivLargeNatP
import FvModexp.Proofs.Arm64.NatQ.DivLargeNatN


set_option autoImplicit false
/-! (Q-form copy of Arm64/Nat/DivLargeNat.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): the call `qhatv := stk.nat(n + 1)` (natdiv.go:651)

`pro2`: from `AtNat` (state `P` at `CALL (*stack).nat`) through the call (premise `StackNatHyp`, as in divmc's
`BasicSqr.pro2`), to the return point with the post facts `AfterNat` handed to a continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : StackNatX.HypQ impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : BitVec 64) (s : State)
    (hpre : Pre R b H L c zp.toNat zc.toNat st.toNat up.toNat uc.toNat ip.toNat il.toNat vp.toNat vl.toNat s)
    (P : State) (hP : AtNat st.toNat up.toNat uc.toNat ip.toNat il.toNat ic.toNat vp.toNat vl.toNat vc.toNat zp.toNat
      zc.toNat s P)
    (hinvP : R.inv b L (s.regs 28).toNat (view R.rt L P.mem)) (Q : State → Prop)
    (k : ∀ S2 L1 b1, AfterNat R b H L st.toNat vl.toNat s P S2 stkSN abSN L1 b1 →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) S2 Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) P Q := by
  by_cases hc0 : 0 < s.mem.readLE (st.toNat + 16) 8
  · exact pro2P impl hap R stkSN abSN hSN hk1 hk2 b L c zp zc st up uc ip il ic vp vl vc s hpre P hP hinvP Q k hc0
  · exact pro2N impl hap R stkSN abSN hSN hk1 hk2 b L c zp zc st up uc ip il ic vp vl vc s hpre P hP hinvP Q k hc0

end FvModexp.Arm64.Q.DivLarge
