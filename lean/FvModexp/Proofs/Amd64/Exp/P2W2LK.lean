import FvModexp.Proofs.Amd64.Exp.P2W2LI

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop theorem at the loop test `LT` (agent divmc s73; amd64 twin of
agent infra's `Arm64.P2W2LK`)

`KS … S M L1 b1 i c yi Z pA lA cA pB lB cB u` bundles the hypotheses of the continuation `KL` (register layout, `LI`,
bounds, parity, budget, model) at one state. `loopKL`: `KL` from three segment premises — the **exit** (`c = 0`,
`i = 0`), the **outer step** (`c = 0`, `i + 1` → `c = 32`, `i`) and the **body** (`c + 1` → `c`), by strong induction
on `33 i + c` (nat.go:1222-1259).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the hypotheses of `KL` at one state -/
structure KS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (r5 : W64) (zzp tp kk cst FV : Nat)
    (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 i c yi Z pA lA cA pB lB cB : Nat) (u : Bool) : Prop where
  epc : S.rip = BitVec.ofNat 64 LT
  esp : S.regs 4 = BitVec.ofNat 64 sp
  e14 : S.regs 14 = BitVec.ofNat 64 g
  e5 : S.regs 5 = r5
  efs : S.fsBase = s.fsBase
  ex : S.xmm 15 = 0
  edf : S.df = false
  em : S.mem = M
  e9 : S.regs 9 = BitVec.ofNat 64 pA
  e6 : S.regs 6 = BitVec.ofNat 64 lA
  e12 : S.regs 12 = BitVec.ofNat 64 cA
  e8 : S.regs 8 = BitVec.ofNat 64 pB
  e1 : S.regs 1 = BitVec.ofNat 64 lB
  e15 : S.regs 15 = BitVec.ofNat 64 cB
  e3 : S.regs 3 = BitVec.ofNat 64 yi
  e10 : S.regs 10 = BitVec.ofNat 64 c - 1#64
  e13 : S.regs 13 = BitVec.ofNat 64 st
  e7 : S.regs 7 = BitVec.ofNat 64 yl
  e11 : S.regs 11 = BitVec.ofNat 64 i
  e2 : S.regs 2 = BitVec.ofNat 64 yp
  e0 : S.regs 0 = BitVec.ofNat 64 lm
  li : LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i u pA lA cA pB lB cB Z
  hi : i < yl
  hyi : yi < 2 ^ 64
  hc : c ≤ 32
  hu : u = true ↔ (c + kk) % 2 = 1
  hb : b + (c + 32 * i) * bc lm + P2Pre.tC lm ≤ b1 + cst
  hfv : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i yi c Z = FV

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

/-- the continuation at the loop test for fixed `i`, `c` -/
@[reducible] def KI (impl : List Amd64.Segment) (ret0 : W64) (Q : State → Prop) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State) (r5 : W64)
    (zzp tp kk cst FV i c : Nat) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 yi Z pA lA cA pB lB cB : Nat) (u : Bool),
    KS R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV S M L1 b1 i c yi Z pA lA cA pB lB cB u →
    ReachesRet (LibW.program.link impl) ret0 S Q

theorem KL_of (H : ∀ i c, KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c) :
    KL impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV := by
  intro S M L1 b1 i c yi Z pA lA cA pB lB cB u epc esp e14 e5 efs ex edf em e9 e6 e12 e8 e1 e15 e3 e10 e13 e7 e11 e2
    e0 li hi hyi hc hu hb hfv
  exact H i c S M L1 b1 yi Z pA lA cA pB lB cB u
    ⟨epc, esp, e14, e5, efs, ex, edf, em, e9, e6, e12, e8, e1, e15, e3, e10, e13, e7, e11, e2, e0, li, hi, hyi, hc, hu,
      hb, hfv⟩

/-- **the loop theorem** (strong induction on `33 i + c`) -/
theorem loopKL
    (hexit : KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV 0 0)
    (hout : ∀ i, KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i 32 →
      KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV (i + 1) 0)
    (hbody : ∀ i c, KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c →
      KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i (c + 1)) :
    KL impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV := by
  have H : ∀ m i c, 33 * i + c = m →
      KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro i c hm
      rcases c with _ | c
      · rcases i with _ | i
        · exact hexit
        · exact hout i (ih (33 * i + 32) (by omega) i 32 rfl)
      · exact hbody i c (ih (33 * i + c) (by omega) i c rfl)
  exact KL_of fun i c => H _ i c rfl

end

end FvModexp.Amd64.P2W2
