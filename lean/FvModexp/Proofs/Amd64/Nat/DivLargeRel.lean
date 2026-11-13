import FvModexp.Proofs.Amd64.Nat.DivLargePro

set_option autoImplicit false

/-!
# `divLarge` (amd64): the segment relations after `v := stk.nat(n)`

The twin of `Arm64/Nat/DivLargeRel.lean`. `AfterNat`: the return of `(*stack).nat` (`callNat + 5`); `Env`: the facts
fixed from then on (scratch `v` at `t`, live set `L1`, budget `b1`, stack array `(w1, c1)`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivLarge

/-- the return address of `CALL (*stack).nat` (`callNat + 5`) -/
abbrev raNat : Nat := 6220357

/-- the facts right after `(*stack).nat` returned (state `S2`; `P` the call state) -/
structure AfterNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st vl : Nat) (s P S2 : State)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  pc : S2.rip = BitVec.ofNat 64 (callNat + 5)
  sp : S2.regs 4 = s.regs 4 - 304#64
  r5 : S2.regs 5 = s.regs 4 - 8#64
  r14 : S2.regs 14 = s.regs 14
  fs : S2.fsBase = s.fsBase
  x15 : S2.xmm 15 = 0#128
  df : S2.df = false
  r0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st + 8 * stLen s.mem st)
  r3 : S2.regs 3 = BitVec.ofNat 64 vl
  r1 : S2.regs 1 = BitVec.ofNat 64 vl
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) vl ≤ b1
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S2.mem)
  ok : StkOK S2.mem R L1 st
  len : stLen S2.mem st = stLen s.mem st + StackNat.rnd vl
  same : stLen s.mem st + StackNat.rnd vl ≤ stCap s.mem st →
    stW S2.mem st = stW s.mem st ∧ stCap S2.mem st = stCap s.mem st
  grow : stCap s.mem st < stLen s.mem st + StackNat.rnd vl →
    InRanges (stW S2.mem st) (8 * stCap S2.mem st) R.rt ∧ ApartAll (stW S2.mem st) (8 * stCap S2.mem st) L
  F2 : MemFrame (P.mem.writeLE ((s.regs 4).toNat - 312) 8 raNat) S2.mem
    (R.rt ++ [((s.regs 4).toNat - 312 - 4192, (s.regs 4).toNat - 312 + 24)] ++ stkWs s.mem st)
  LF2 : LiveFrame (P.mem.writeLE ((s.regs 4).toNat - 312) 8 raNat) S2.mem L (stkWs s.mem st)
  mem : stCap s.mem st < stLen s.mem st + StackNat.rnd vl →
    (stW S2.mem st, stW S2.mem st + 8 * stCap S2.mem st) ∈ L1
  reg : S2.mem.regions = s.mem.regions

/-- the facts fixed from the `stk.nat` call on: the scratch `v` at `t` (`n` words), the live set `L1`, the budget `b1`,
the stack array `(w1, c1)` -/
structure Env (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b L c zp zc st up uc ip il vp vl s
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t vl
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) vl ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + StackNat.rnd vl ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1
  arrL : ¬(w1 = stW s.mem st ∧ c1 = stCap s.mem st) → (w1, w1 + 8 * c1) ∈ L1 ∧ 0 < c1
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  ra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

/-- `Env` from `stk.nat`'s post (pure) -/
theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (hpre : Pre R b L c zp zc st up uc ip il vp vl s) {S2 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hext : LiveExt R L L1) (hbud : b - stackNatCost (stLen s.mem st) vl ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen s.mem st + StackNat.rnd vl)
    (hsame : stLen s.mem st + StackNat.rnd vl ≤ stCap s.mem st → stW S2 st = stW s.mem st ∧ stCap S2 st = stCap s.mem st)
    (hgrow : stCap s.mem st < stLen s.mem st + StackNat.rnd vl → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = s.mem.accessible a n v)
    (hmem : stCap s.mem st < stLen s.mem st + StackNat.rnd vl → (stW S2 st, stW S2 st + 8 * stCap S2 st) ∈ L1)
    (hx : s.xmm 15 = 0#128) (hdf : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    Env R b L c zp zc st up uc ip il vp vl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have hv2 := hpre.v2
  have hscr := Scr.of_post (m0 := s.mem) (k := vl) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_, ?_, hx, hdf, hra⟩
  · rw [← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + StackNat.rnd vl ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hacc2]; exact a3, a4⟩
  · exact (ArrIn.of_nat (L1 := L1) (m0 := s.mem) (m := S2) hlc hlen hsame hmem :)

end FvModexp.Amd64.DivLarge
