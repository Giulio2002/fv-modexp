import FvModexp.Proofs.Amd64.Exp.P2W2PQ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the facts after the table (`AT`, at `ppRet` = fn+0x289) (agent divmc s68;
amd64 twin of agent infra's `Arm64.P2W2AT`)

Stack levels: `lvlR = ℓ₀ + 8w` (`reserve(8w)`), `lvlZ = lvlR + rnd(2w)` (`zz = stk.nat(2w)`), `lvlL = lvlZ + rnd(5w)`
(the table's `buf`); the cost so far `cost0`. `AT` = `WC` at level `lvlL` + the slots `ESl` + `zz` (slots
`0x118/0x68/0x70`, a scratch nat of `2w` words relative to the entry, `BU`) + the table (`powers[j]`, `j < 4`, headers at
`sp + 0x140`, in `buf`, scratch, `BU`) + `zz` apart from `buf`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

@[reducible] def lvlR (ℓ0 lm : Nat) : Nat := ℓ0 + 8 * W lm
@[reducible] def lvlZ (ℓ0 lm : Nat) : Nat := lvlR ℓ0 lm + StackNat.rnd (2 * W lm)
@[reducible] def lvlL (ℓ0 lm : Nat) : Nat := lvlZ ℓ0 lm + StackNat.rnd (P2Pre.NB 4 lm)

/-- `HW` is `buildPrecomputationWindowModPower2`'s reserve level at its entry (`lvlZ`) -/
theorem hw_eq (ℓ0 lm : Nat) : HW ℓ0 lm = P2Pre.HP (lvlZ ℓ0 lm) 4 lm := rfl

/-- the loop's `sqr`/`mul` level twin: at `lvlL`, operands of at most `2 w` words in all fit `HW` -/
theorem lvl_twin {ℓ0 lm l a : Nat} (h : l = lvlL ℓ0 lm) (ha : a ≤ 2 * W lm) : l + 4 * a + 64 ≤ HW ℓ0 lm := by
  subst h; simp only [HW, lvlL, lvlZ, lvlR, P2Pre.NB, P2Pre.W, W, StackNat.rnd, Nat.reduceAdd] at ha ⊢; omega

/-- the cost up to the table's return (the two `stk` operations are paid by the reserve) -/
@[reducible] def cost0 (lm : Nat) : Nat := P2Pre.cost 4 lm

/-- the facts after the table (see the module doc) -/
structure AT (R : RtInv) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (M : Memory) (L3 : List (Nat × Nat)) (b3 zzp tp : Nat) : Prop where
  wc : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L3 b3 (lvlL (stLen s.mem st) lm)
  esl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)
  z118 : M.readLE (sp + 0x118) 8 = zzp
  z68 : M.readLE (sp + 0x68) 8 = 2 * W lm
  z70 : M.readLE (sp + 0x70) 8 = 2 * W lm
  zscr : Scr R L L3 s.mem M st zzp (2 * W lm)
  zbu : P2Pre.BU M st zzp (8 * (2 * W lm))
  pw : ∀ j, j < 4 → P2Pre.PwD M (sp + 0x140) tp lm (natVal s.mem xp xl) j
  bscr : Scr R L L3 s.mem M st tp (P2Pre.NB 4 lm)
  bbu : P2Pre.BU M st tp (8 * P2Pre.NB 4 lm)
  zb : Apart zzp (8 * (2 * W lm)) tp (8 * P2Pre.NB 4 lm)

/-- a scratch nat through a step that keeps accessibility, with a larger live set -/
theorem Scr.mono {R : RtInv} {L L1 L2 : List (Nat × Nat)} {m0 M M' : Memory} {st t k : Nat}
    (h : Scr R L L1 m0 M st t k) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hx : LiveExt R L1 L2) :
    Scr R L L2 m0 M' st t k :=
  ⟨h.b48, by rw [hacc]; exact h.acc, h.al, hx.held h.held, h.loc⟩

/-- the slot ranges of `ESl` (`ESl.keep`'s condition) -/
@[reducible] def SlotC (sp a k : Nat) : Prop :=
  sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58 ∨ sp + 0x100 ≤ a ∧ a + k ≤ sp + 0x118 ∨
    sp + 0x1a0 ≤ a ∧ a + k ≤ sp + 0x1b8 ∨ sp + 0x1c0 ≤ a ∧ a + k ≤ sp + 0x230

theorem slot_in {sp a k : Nat} (h : SlotC sp a k) : sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x230 := by
  simp only [SlotC] at h; omega

/-- the slots are outside a callee window at `RSP = sp - 8` (`above ≤ 0x5f`: return address + spill words below
`sp + 0x57`) -/
theorem slot_callee {sp a k x above : Nat} (h : SlotC sp a k) (hx : 8 ≤ sp) (ha : above ≤ 0x5f) :
    Outside a k [(sp - 8 - x, sp - 8 + above)] := by
  simp only [SlotC] at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the stores of `segN` (return address, zz's header, `powers`) -/
@[reducible] def NW (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x68, sp + 0x78), (sp + 0x118, sp + 0x120), (sp + 0x140, sp + 0x1a0)]

/-- the slots are outside the stores of `segN` -/
theorem slot_n {sp a k : Nat} (h : SlotC sp a k) : Outside a k (NW sp) := by
  simp only [SlotC] at h; simp only [NW, outside_cons, outside_nil, and_true]; omega

theorem slot_pw {sp a k : Nat} (h : SlotC sp a k) : Outside a k [(sp + 0x140, sp + 0x1a0)] := by
  simp only [SlotC] at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the new nat of `stk.nat(n)` (`0 < n`): its pointer and `BU` -/
theorem zz_post {R : RtInv} {L : List (Nat × Nat)} {M : Memory} {st ℓ n : Nat} (hok : StkOK M R L st)
    (hlen : stLen M st = ℓ + StackNat.rnd n) (hn : 0 < n) {r : BitVec 64}
    (hz0 : r = BitVec.ofNat 64 (stW M st + 8 * ℓ)) :
    r.toNat = stW M st + 8 * ℓ ∧ P2Pre.BU M st (stW M st + 8 * ℓ) (8 * n) := by
  obtain ⟨-, -, -, -, hzl, hzlc, -⟩ := hok
  simp only [StackNat.rnd] at hlen
  have hcap0 : 0 < stCap M st := by omega
  have hz48 := (hzl hcap0).2.2.2
  refine ⟨?_, Or.inl ⟨by omega, by omega⟩⟩
  rw [hz0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- a window range the function writes: inside `WN` -/
@[reducible] def InWN (sp K : Nat) (r : Nat × Nat) : Prop :=
  sp - 8 - K ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 0x230 ∧ (r.2 ≤ sp + 0x1d0 ∨ sp + 0x1f0 ≤ r.1)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- `WC` through stores into window ranges `ws` (outside the caller's return address and `y`) -/
theorem WC.win (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    {M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ r ∈ ws, InWN sp K r) :
    WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M' L1 b1 ℓ := by
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw : Apart st 24 (sp - 8 - K) (K + 0x238) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  refine h.frame hF hrg (fun a k ho => ?_) (fun a k hin _ => ?_) ?_ (fun r hr => Or.inr ?_)
  · rw [outside_append, outside_append] at ho
    have := ho.1.2
    simp only [WN, outside_cons, outside_nil, and_true] at this
    refine outside_of_forall fun r hr => ?_
    have := hws r hr; simp only [InWN] at this; omega
  · obtain ⟨r0, hr0, q1, q2⟩ := hin
    have := hLs r0 hr0
    simp only [outside_cons, outside_nil, and_true] at this
    refine outside_of_forall fun r hr => ?_
    have := hws r hr; simp only [InWN] at this; omega
  · refine outside_of_forall fun r hr => ?_
    have := hws r hr; simp only [InWN] at this; omega
  · have := hws r hr
    simp only [InWN] at this
    exact hout.of_sub (by omega) (by omega)

end

theorem nseg_ws (sp K : Nat) (hK : 8 + K ≤ sp) : ∀ r ∈ NW sp, InWN sp K r := by
  intro r hr
  simp only [NW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [InWN] <;> omega

theorem hdr_nseg {st sp K : Nat} (h : Apart st 24 (sp - 8 - K) (K + 0x238)) (hK : 8 + K ≤ sp) :
    Outside st 24 (NW sp) := by
  unfold Apart at h; simp only [NW, outside_cons, outside_nil, and_true]; omega

end FvModexp.Amd64.P2W2
