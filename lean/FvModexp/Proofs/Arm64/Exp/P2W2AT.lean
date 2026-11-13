import FvModexp.Proofs.Arm64.Exp.P2W2PP

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the facts after the table (`AT`, at `0x1b65f4 = 1795572`) (agent infra)

Stack levels: `lvlR = ℓ₀ + 8w` (`reserve(8w)` consumes `8w`), `lvlZ = lvlR + rnd(2w)` (`zz = stk.nat(2w)`),
`lvlL = lvlZ + rnd(5w)` (the table's `buf`); the cost so far `cost0`. `AT` = `WC` at level `lvlL` + the slots `ESl` + `zz`
(slots `280/112/120`, a scratch nat of `2w` words relative to the entry, `BU`) + the table (`powers[j]`, `j < 4`, in
`buf`, scratch, `BU`) + `zz` apart from `buf`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

@[reducible] def lvlR (ℓ0 lm : Nat) : Nat := ℓ0 + 8 * W lm
@[reducible] def lvlZ (ℓ0 lm : Nat) : Nat := lvlR ℓ0 lm + StackNat.rnd (2 * W lm)
@[reducible] def lvlL (ℓ0 lm : Nat) : Nat := lvlZ ℓ0 lm + StackNat.rnd (P2Pre.NB 4 lm)

/-- the cost up to the table's return -/
@[reducible] def cost0 (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ0 lm : Nat) : Nat :=
  stackNatCost ℓ0 (8 * W lm) + stackNatCost (lvlR ℓ0 lm) (2 * W lm) + P2Pre.cost sqC mlC (lvlZ ℓ0 lm) 4 lm

/-- the facts after the table (see the module doc) -/
structure AT (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (M : Memory) (L3 : List (Nat × Nat)) (b3 zzp bp : Nat) : Prop where
  wc : WC R L K g sp st zp zc s.mem M L3 b3 (lvlL (stLen s.mem st) lm)
  esl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st)
  z280 : M.readLE (sp + 280) 8 = zzp
  z112 : M.readLE (sp + 112) 8 = 2 * W lm
  z120 : M.readLE (sp + 120) 8 = 2 * W lm
  zscr : Scr R L L3 s.mem M st zzp (2 * W lm)
  zbu : P2Pre.BU M st zzp (8 * (2 * W lm))
  pw : ∀ j, j < 4 → P2Pre.PwD M (sp + 320) bp lm (natVal s.mem xp xl) j
  bscr : Scr R L L3 s.mem M st bp (P2Pre.NB 4 lm)
  bbu : P2Pre.BU M st bp (8 * P2Pre.NB 4 lm)
  zb : Apart zzp (8 * (2 * W lm)) bp (8 * P2Pre.NB 4 lm)

/-- a scratch nat through a step that keeps accessibility, with a larger live set -/
theorem Scr.mono {R : RtInv} {L L1 L2 : List (Nat × Nat)} {m0 M M' : Memory} {st t k : Nat}
    (h : Scr R L L1 m0 M st t k) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hx : LiveExt R L1 L2) :
    Scr R L L2 m0 M' st t k :=
  ⟨h.b48, by rw [hacc]; exact h.acc, h.al, hx.held h.held, h.loc⟩

/-- the slot ranges of `ESl` (`ESl.keep`'s condition) -/
@[reducible] def SlotC (sp a k : Nat) : Prop :=
  sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 95 ≤ a ∧ a + k ≤ sp + 96 ∨ sp + 256 ≤ a ∧ a + k ≤ sp + 280 ∨
    sp + 416 ≤ a ∧ a + k ≤ sp + 456 ∨ sp + 472 ≤ a ∧ a + k ≤ sp + 560

theorem slot_in {sp a k : Nat} (h : SlotC sp a k) : sp - 8 ≤ a ∧ a + k ≤ sp + 560 := by
  simp only [SlotC] at h; omega

/-- the slots are outside a callee window at `SP = sp` (`above ≤ 88`) -/
theorem slot_callee {sp a k x above : Nat} (h : SlotC sp a k) (hx : 8 ≤ sp) (ha : above ≤ 88) :
    Outside a k [(sp - x, sp - 8), (sp + 8, sp + above)] := by
  simp only [SlotC] at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the slots are outside the stores of `segN` (zz's header, `powers`) -/
theorem slot_n {sp a k : Nat} (h : SlotC sp a k) (hx : 8 ≤ sp) :
    Outside a k [(sp + 112, sp + 128), (sp + 280, sp + 288), (sp + 320, sp + 416)] := by
  simp only [SlotC] at h; simp only [outside_cons, outside_nil, and_true]; omega

theorem slot_pw {sp a k : Nat} (h : SlotC sp a k) : Outside a k [(sp + 320, sp + 416)] := by
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

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- `WC` through stores into window ranges `ws` (outside the caller's saved FP/LR) -/
theorem WC.win (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ r ∈ ws, sp - K ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 560 ∧ (r.2 ≤ sp + 456 ∨ sp + 472 ≤ r.1)) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  refine h.frame hF hrg (fun a k ho => ?_) (fun a k hin _ => ?_) ?_ (fun r hr => Or.inr ?_)
  · rw [outside_append, outside_append] at ho
    have := ho.1.2
    simp only [WN, outside_cons, outside_nil, and_true] at this
    refine outside_of_forall fun r hr => ?_
    have := hws r hr; omega
  · obtain ⟨r0, hr0, q1, q2⟩ := hin
    have := hLs r0 hr0
    simp only [outside_cons, outside_nil, and_true] at this
    refine outside_of_forall fun r hr => ?_
    have := hws r hr; omega
  · refine outside_of_forall fun r hr => ?_
    have := hws r hr; omega
  · have := hws r hr
    exact hout.of_sub (by omega) (by omega)

end

theorem nseg_ws (sp K : Nat) : ∀ r ∈ [(sp + 112, sp + 128), (sp + 280, sp + 288), (sp + 320, sp + 416)],
    sp - K ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 560 ∧ (r.2 ≤ sp + 456 ∨ sp + 472 ≤ r.1) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega

theorem hdr_nseg {st sp K a k : Nat} (h : Apart st 24 (sp - K) (K + 560)) (hK : K ≤ sp) (h1 : st ≤ a)
    (h2 : a + k ≤ st + 24) : Outside a k [(sp + 112, sp + 128), (sp + 280, sp + 288), (sp + 320, sp + 416)] := by
  unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega

end FvModexp.Arm64.P2W2
