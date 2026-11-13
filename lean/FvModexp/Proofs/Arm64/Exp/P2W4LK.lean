import FvModexp.Proofs.Arm64.Exp.P2W4UB
import FvModexp.Proofs.Arm64.Exp.P2W4Mv

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the loop theorem at the loop test `LT` (agent infra)

`KS … S M L1 b1 i c yi Z pA lA cA pB lB cB u` bundles the hypotheses of the continuation `KL` (register layout, `LI`,
bounds, parity, budget, model) at one state. `loopKL`: `KL` from three segment premises — the **exit** (`c = 0`,
`i = 0`), the **outer step** (`c = 0`, `i + 1` → `c = 16`, `i`) and the **body** (`c + 1` → `c`), by strong induction
on `17 i + c` (nat.go:1222-1259).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

/-- the hypotheses of `KL` at one state -/
structure KS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat) (zzp bp kk cst FV : Nat)
    (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 i c yi Z pA lA cA pB lB cB : Nat) (u : Bool) : Prop where
  epc : S.pc = BitVec.ofNat 64 LT
  esp : S.sp = BitVec.ofNat 64 sp
  e28 : S.regs 28 = BitVec.ofNat 64 g
  e29 : S.regs 29 = r29
  e18 : S.regs 18 = s.regs 18
  em : S.mem = M
  e3 : S.regs 3 = BitVec.ofNat 64 pA
  e1 : S.regs 1 = BitVec.ofNat 64 lA
  e14 : S.regs 14 = BitVec.ofNat 64 cA
  e0 : S.regs 0 = BitVec.ofNat 64 pB
  e15 : S.regs 15 = BitVec.ofNat 64 lB
  e13 : S.regs 13 = BitVec.ofNat 64 cB
  e8 : S.regs 8 = BitVec.ofNat 64 yi
  e7 : S.regs 7 = BitVec.ofNat 64 c - 1#64
  e4 : S.regs 4 = BitVec.ofNat 64 kk - 2#64
  e9 : S.regs 9 = BitVec.ofNat 64 st
  e10 : S.regs 10 = BitVec.ofNat 64 yl
  e11 : S.regs 11 = BitVec.ofNat 64 i
  e12 : S.regs 12 = BitVec.ofNat 64 yp
  e2 : S.regs 2 = BitVec.ofNat 64 lm
  li : LI R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp kk i u pA lA cA pB lB cB Z
  hi : i < yl
  hyi : yi < 2 ^ 64
  hc : c ≤ 16
  hu : u = true ↔ (c + kk) % 2 = 1
  hb : b + (c + 16 * i) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm + P2Pre.tC lm ≤ b1 + cst
  hfv : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i yi c Z = FV

/-- value and normal form of `p[0:l]` through a step keeping its bytes -/
theorem nv_keep {M M' : Memory} {p l : Nat}
    (hk : ∀ a k, p ≤ a → a + k ≤ p + 8 * l → M'.readLE a k = M.readLE a k) :
    natVal M' p l = natVal M p l ∧ (NatNorm M p l → NatNorm M' p l) := by
  refine ⟨hk p (8 * l) (Nat.le_refl _) (Nat.le_refl _), fun h => ?_⟩
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact Or.inl h0
  rcases h with h | h
  · exact Or.inl h
  · right; rw [hk _ _ (by omega) (by omega)]; exact h

/-- a nat of odd value has a positive length -/
theorem len_pos {M : Memory} {p l Z : Nat} (hv : natVal M p l = Z) (hz : Z % 2 = 1) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; simp at hv; omega
  · exact h0

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

theorem BC.keep {M M' : Memory} {L1 L2 : List (Nat × Nat)} {zzp bp : Nat} {u : Bool} {p c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u p c) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hx : LiveExt R L1 L2) (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st)
    (e2 : stCap M' st = stCap M st) : BC R L K g sp st zp zc M' L2 zzp bp lm u p c := by
  cases u
  · exact h
  · exact UB.keep h hacc hx e0 e1 e2

/-- a buffer of either class (positive cap) is apart from the window -/
theorem BC.win (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {zzp bp X : Nat} (htz : TZ R L s.mem M L1 st sp zzp bp lm X) {u : Bool} {p c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u p c) (hc : 0 < c) : Apart p (8 * c) (sp - K) (K + 848) := by
  cases u
  · obtain ⟨rfl, rfl⟩ := h; exact scr_win hP htz.zscr
  · exact (h.ap hc).1

set_option maxRecDepth 20000 in
/-- `LI` through the function's own stores into window slots (not the `ESl` slots, `200`, the table headers) -/
theorem LI.win (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {ret : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 zzp bp kk i : Nat} {u : Bool} {pA lA cA pB lB cB Z : Nat}
    (h : LI R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp kk i u pA lA cA pB lB cB Z)
    {M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ r ∈ ws, sp + 96 ≤ r.1 ∧ r.1 ≤ r.2 ∧ (r.2 ≤ sp + 200 ∨ sp + 208 ≤ r.1) ∧
      (r.2 ≤ sp + 256 ∨ sp + 280 ≤ r.1 ∧ r.2 ≤ sp + 320))
    {i' : Nat} (r208 : M'.readLE (sp + 208) 8 = i') :
    LI R L K g sp st zp zc xp xl xc yp yl lm ret s M' L1 b1 zzp bp kk i' u pA lA cA pB lB cB Z := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 848) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a k, (a + k ≤ sp + 96 ∨ sp + 848 ≤ a ∨ (sp + 200 ≤ a ∧ a + k ≤ sp + 208) ∨
      (sp + 256 ≤ a ∧ a + k ≤ sp + 280) ∨ sp + 320 ≤ a) → M'.readLE a k = M.readLE a k := fun a k ha =>
    hF.readLE a k (outside_of_forall fun r hr => by have := hws r hr; omega)
  have hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w := hF.accessible
  have e0 : stW M' st = stW M st := hrd _ _ (by omega)
  have e1 : stLen M' st = stLen M st := hrd _ _ (by omega)
  have e2 : stCap M' st = stCap M st := hrd _ _ (by omega)
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have hlA := len_pos h.va h.zo
  have hAW := BC.win hP h.tz h.ca (by have := h.lac; omega)
  unfold Apart at hAW
  obtain ⟨v1, v2⟩ := nv_keep (M := M) (M' := M') (p := pA) (l := lA) fun a k h1 h2 => hrd a k (by
    have := h.lac; omega)
  exact ⟨WC.win hP h.wc hF hrg (fun r hr => by have := hws r hr; omega),
    ESl.keep h.esl (fun a k ha => hrd a k (by omega)) (by omega), by rw [hrd _ _ (by omega)]; exact h.s200, r208,
    h.tz.keep hacc (LiveExt.refl R L1) e0 e1 e2 (fun a k ha => hrd a k (by omega)), h.la, h.lac, h.lbc,
    v1.trans h.va, v2 h.na, h.ca.keep hacc (LiveExt.refl R L1) e0 e1 e2,
    h.cb.keep hacc (LiveExt.refl R L1) e0 e1 e2, h.zo, h.cb0⟩

end

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat}
    {mlC : Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

/-- the continuation at the loop test for fixed `i`, `c` -/
@[reducible] def KI (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State) (r29 : BitVec 64)
    (sqC : Nat → Nat) (mlC : Nat → Nat → Nat) (zzp bp kk cst FV i c : Nat) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 yi Z pA lA cA pB lB cB : Nat) (u : Bool),
    KS R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV S M L1 b1 i c yi Z pA lA cA pB lB cB u →
    ReachesRet (LibW.program.link impl) ret0 S Q

theorem KL_of (H : ∀ i c, KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c) :
    KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV := by
  intro S M L1 b1 i c yi Z pA lA cA pB lB cB u epc esp e28 e29 e18 em e3 e1 e14 e0 e15 e13 e8 e7 e4 e9 e10 e11 e12 e2
    li hi hyi hc hu hb hfv
  exact H i c S M L1 b1 yi Z pA lA cA pB lB cB u
    ⟨epc, esp, e28, e29, e18, em, e3, e1, e14, e0, e15, e13, e8, e7, e4, e9, e10, e11, e12, e2, li, hi, hyi, hc, hu, hb,
      hfv⟩

/-- **the loop theorem** (strong induction on `17 i + c`) -/
theorem loopKL
    (hexit : KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV 0 0)
    (hout : ∀ i, KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i 16 →
      KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV (i + 1) 0)
    (hbody : ∀ i c, KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c →
      KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i (c + 1)) :
    KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV := by
  have H : ∀ m i c, 17 * i + c = m →
      KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro i c hm
      rcases c with _ | c
      · rcases i with _ | i
        · exact hexit
        · exact hout i (ih (17 * i + 16) (by omega) i 16 rfl)
      · exact hbody i c (ih (17 * i + c) (by omega) i c rfl)
  exact KL_of fun i c => H _ i c rfl

end

end FvModexp.Arm64.P2W4
