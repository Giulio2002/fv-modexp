import FvModexp.Proofs.Common.StackNatMath

set_option autoImplicit false

/-!
# Amortised stack growth: the stack potential (ISA independent; divmc, TIGHT COSTS)

`(*stack).nat(n)` grows the stack array (`growslice`, Janus charges `8 · c'` bytes for the new capacity `c'`) only when
the level `len + nr` exceeds the capacity `c`. Charging every call the worst case (`stackNatCost len n`, a full-stack
copy) makes every stack user's cost depend on the stack level and multiplies it by the number of calls. Instead the
capacity holds CREDIT `potK · cap`: a growth multiplies the capacity by at least `5/4` (`nextslicecap`), so
`8 · c' ≤ potK · (c' − c)` (`grow_amort`): the credit of the added words pays the copy.

**Q-form** of a stack user's budget (NOTES-conventions "[divmc s34] TIGHT COSTS step 2"): a parameter `H` (a bound of
every stack level the call reaches: its level bound `stLen + D ≤ 2^16` gets the twin `stLen + D ≤ H`) and a
level-free consumption `C` (no stack terms):
* pre  `C + stkR H s.mem st ≤ b`
* post `b - stkR H s.mem st - C + stkR H s'.mem st ≤ b'`
`stkR H m st = stkRes H - potK · stCap m st` is the part of the reserve `stkRes H` not yet held in the capacity.
Sequential calls with the same `H` compose by adding the `C`s (`q_seq`); the reserve is never consumed.
A caller that owns the stack (`stk == nil`: getStack … free) states the plain form `b - stkRes H - C ≤ b'` (`q_plain`).
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Contracts

/-- bytes of credit per word of stack capacity -/
abbrev potK : Nat := 40

/-- a bound of the capacity after a growth to a level `≤ H` (`8 · growCap8 ≤ stackNatCost len n`) -/
def capB (H : Nat) : Nat := 4 * H + 11

/-- the stack reserve for levels `≤ H` -/
def stkRes (H : Nat) : Nat := potK * capB H

/-- the part of the reserve not yet held in the stack's capacity -/
def stkR (H : Nat) (m : Memory) (st : Nat) : Nat := stkRes H - potK * stCap m st

theorem stkR_le (H : Nat) (m : Memory) (st : Nat) : stkR H m st ≤ stkRes H := by
  unfold stkR; omega

theorem stkR_congr {H : Nat} {m m' : Memory} {st : Nat} (h : stCap m' st = stCap m st) :
    stkR H m' st = stkR H m st := by
  unfold stkR; rw [h]

theorem stkR_of_cap {H : Nat} {m : Memory} {st c : Nat} (h : stCap m st = c) : stkR H m st = stkRes H - potK * c := by
  unfold stkR; rw [h]

/-- the reserve is monotone in `H` -/
theorem stkR_mono {H H' : Nat} (h : H ≤ H') (m : Memory) (st : Nat) : stkR H m st ≤ stkR H' m st := by
  simp only [stkR, stkRes, capB, potK]; omega

theorem stkRes_eq (H : Nat) : stkRes H = 160 * H + 440 := by simp only [stkRes, capB, potK]; omega

/-! ## Growth facts -/

private theorem go_ge (N : Nat) : ∀ c, 5 * c ≤ 4 * nextslicecap.go N c := by
  intro c
  induction c using nextslicecap.go.induct N with
  | case1 c c' hc' => unfold nextslicecap.go; simp only [c'] at *; split <;> omega
  | case2 c c' hc' ih => unfold nextslicecap.go; simp only [c'] at *; split
                         · omega
                         · omega

/-- `nextslicecap` grows a capacity by at least `5/4` -/
theorem nextslicecap_ge (N c : Nat) (h : c < N) : 5 * c ≤ 4 * nextslicecap N c := by
  unfold nextslicecap
  split
  · omega
  · split
    · omega
    · exact go_ge N c

theorem nextslicecap_le_growCap8 (N c : Nat) : nextslicecap N c ≤ growCap8 N c := by
  unfold growCap8
  have h2 := le_roundupsize (nextslicecap N c * 8) true
  exact (Nat.le_div_iff_mul_le (by decide)).2 (by omega)

/-- **amortisation**: a growth from `c < N` is paid by the credit of the added words -/
theorem grow_amort (N c : Nat) (h : c < N) : 8 * growCap8 N c ≤ potK * (growCap8 N c - c) := by
  have h1 := nextslicecap_ge N c h
  have h2 := nextslicecap_le_growCap8 N c
  simp only [potK]; omega

/-- the capacity after `stk.nat(n)`'s growth at level `len` is at most `capB H` (`len + n + 3 ≤ H`) -/
theorem growCap8_le_capB (len n c H : Nat) (hc : c < len + (n + 3) / 4 * 4) (hH : len + n + 3 ≤ H) :
    growCap8 (len + (n + 3) / 4 * 4) c ≤ capB H := by
  have := growRound_le_cost len n c hc
  unfold stackNatCost allocCost at this
  unfold capB; omega

/-- **`stk.nat(n)`'s budget step** (growth case): the reserve pays the block, and the Q-form post holds -/
theorem grow_bud (len n c H b : Nat) (hc : c < len + (n + 3) / 4 * 4) (hH : len + n + 3 ≤ H)
    (hb : stkRes H - potK * c ≤ b) :
    8 * growCap8 (len + (n + 3) / 4 * 4) c ≤ b ∧
      b - (stkRes H - potK * c) + (stkRes H - potK * growCap8 (len + (n + 3) / 4 * 4) c) ≤
        b - 8 * growCap8 (len + (n + 3) / 4 * 4) c := by
  have h1 := grow_amort (len + (n + 3) / 4 * 4) c hc
  have h2 := growCap8_le_capB len n c H hc hH
  have h3 := le_growCap8 (len + (n + 3) / 4 * 4) c
  generalize growCap8 (len + (n + 3) / 4 * 4) c = g at *
  simp only [stkRes, capB, potK] at *
  constructor <;> omega

/-! ## Composition -/

/-- two sequential Q-form calls with the same `H` (the middle memories may differ outside the header: `hc`) -/
theorem q_seq {H b b1 b1' b2 C1 C2 : Nat} {m0 m1 m1' m2 : Memory} {st : Nat}
    (h1 : b - stkR H m0 st - C1 + stkR H m1 st ≤ b1) (hc : stCap m1' st = stCap m1 st)
    (h2 : b1' - stkR H m1' st - C2 + stkR H m2 st ≤ b2) (hb1 : b1 ≤ b1') (hpre : C1 + C2 + stkR H m0 st ≤ b) :
    b - stkR H m0 st - (C1 + C2) + stkR H m2 st ≤ b2 := by
  rw [stkR_congr hc] at h2; omega

/-- the pre of the second call of a sequence -/
theorem q_pre2 {H b b1 b1' C1 C2 : Nat} {m0 m1 m1' : Memory} {st : Nat}
    (h1 : b - stkR H m0 st - C1 + stkR H m1 st ≤ b1) (hc : stCap m1' st = stCap m1 st) (hb1 : b1 ≤ b1')
    (hpre : C1 + C2 + stkR H m0 st ≤ b) : C2 + stkR H m1' st ≤ b1' := by
  rw [stkR_congr hc]; omega

/-- the plain form for a caller that owns the stack -/
theorem q_plain {H b b' C : Nat} {m m' : Memory} {st : Nat} (h : b - stkR H m st - C + stkR H m' st ≤ b') :
    b - stkRes H - C ≤ b' := by
  have := stkR_le H m st; omega

/-- a Q-form pre at a larger `H'` (a callee bound `H ≤ H'` is not needed: pass the caller's `H`) -/
theorem q_pre_of_plain {H b C : Nat} {m : Memory} {st : Nat} (h : C + stkRes H ≤ b) : C + stkR H m st ≤ b := by
  have := stkR_le H m st; omega

end FvModexp
