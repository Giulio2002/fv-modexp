import FvModexp.Proofs.Arm64.Exp.P2W2UB

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the loop theorem at the loop test `LT` (agent infra)

`KS … S M L1 b1 i c yi Z pA lA cA pB lB cB u` bundles the hypotheses of the continuation `KL` (register layout, `LI`,
bounds, parity, budget, model) at one state. `loopKL`: `KL` from three segment premises — the **exit** (`c = 0`,
`i = 0`), the **outer step** (`c = 0`, `i + 1` → `c = 32`, `i`) and the **body** (`c + 1` → `c`), by strong induction
on `33 i + c` (nat.go:1222-1259).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the hypotheses of `KL` at one state -/
structure KS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (r29 : BitVec 64) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (zzp bp kk cst FV : Nat)
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
  e13 : S.regs 13 = BitVec.ofNat 64 lB
  e15 : S.regs 15 = BitVec.ofNat 64 cB
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
  hc : c ≤ 32
  hu : u = true ↔ (c + kk) % 2 = 1
  hb : b + (c + 32 * i) * bc sqC mlC (ℓL (stLen s.mem st) lm) lm + P2Pre.tC lm ≤ b1 + cst
  hfv : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i yi c Z = FV

section
variable {impl : List Segment} {ret0 : BitVec 64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st zp zc xp xl xc yp yl lm ret : Nat} {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat}
    {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}

/-- the continuation at the loop test for fixed `i`, `c` -/
@[reducible] def KI (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State) (r29 : BitVec 64)
    (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (zzp bp kk cst FV i c : Nat) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 yi Z pA lA cA pB lB cB : Nat) (u : Bool),
    KS R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV S M L1 b1 i c yi Z pA lA cA pB lB cB u →
    ReachesRet (LibExp.program.link impl) ret0 S Q

theorem KL_of (H : ∀ i c, KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c) :
    KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV := by
  intro S M L1 b1 i c yi Z pA lA cA pB lB cB u epc esp e28 e29 e18 em e3 e1 e14 e0 e13 e15 e8 e7 e4 e9 e10 e11 e12 e2
    li hi hyi hc hu hb hfv
  exact H i c S M L1 b1 yi Z pA lA cA pB lB cB u
    ⟨epc, esp, e28, e29, e18, em, e3, e1, e14, e0, e13, e15, e8, e7, e4, e9, e10, e11, e12, e2, li, hi, hyi, hc, hu, hb,
      hfv⟩

/-- **the loop theorem** (strong induction on `33 i + c`) -/
theorem loopKL
    (hexit : KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV 0 0)
    (hout : ∀ i, KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i 32 →
      KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV (i + 1) 0)
    (hbody : ∀ i c, KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c →
      KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i (c + 1)) :
    KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV := by
  have H : ∀ m i c, 33 * i + c = m →
      KI impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV i c := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i c hm
      rcases c with _ | c
      · rcases i with _ | i
        · exact hexit
        · exact hout i (ih (33 * i + 32) (by omega) i 32 rfl)
      · exact hbody i c (ih (33 * i + c) (by omega) i c rfl)
  exact KL_of fun i c => H _ i c rfl

end

end FvModexp.Arm64.P2W2
