import FvModexp.Proofs.Amd64.Exp.P2W2AT

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop invariant at the loop test `LT` (fn+0x7d1) (agent divmc s70;
amd64 twin of agent infra's `Arm64.P2W2LI`)

`LT` = fn+0x7d1 (`MOVQ R9, 0x118(SP)`; `MOVQ SI, 0x68(SP)`; `TESTQ R10, R10` at +0x7e0, `JGE` body +0x645). Every
entry (first window from `z.set` via +0x625 → +0x635 → `JMP LT`; the body's back edge at +0x7a0..; the outer loop's
`i--` at +0x627..+0x640 → `JMP LT`) reaches `LT` with: `z = (R9, SI, R12)`, `zz = (R8, CX, R15)`, `BX = yi` (shifted),
`R10 = c - 1` (signed; `k` of nat.go:1222), `R11 = i`, `DI = len y`, `DX = y`, `AX = logM`, `R13 = stk`; slots
`0xc0 = kk - 2` (`oddNumberOfSwaps` = bit 0 clear, nat.go:1213), `0xc8 = i`.

Buffer classes as in `Arm64.P2W2LI` (`BC u`: U-class = entry `z` or fresh runtime object, S-class = `zz`'s stack
buffer `(zzp, 2w)`; `z` class `u`, `zz` class `!u`, a body flips `u`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the loop test (fn+0x7d1) -/
abbrev LT : Nat := 6202865

/-- the U-class buffer `(p, c)` at memory `M`, live set `L1` -/
structure UB (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (zzp bp lm p c : Nat) : Prop where
  c40 : c < 2 ^ 40
  live : NatLive M R L1 p c
  org : (p = zp ∧ c = zc) ∨ (0 < c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  ap : 0 < c → Apart p (8 * c) (sp - 8 - K) (K + 0x238) ∧ Apart p (8 * c) st 24 ∧ Apart p (8 * c) RunIface.gA 32 ∧
    Apart p (8 * c) (g + 16) 8 ∧ Apart p (8 * c) (free M st).1 (free M st).2 ∧
    Apart p (8 * c) zzp (8 * (2 * W lm)) ∧ Apart p (8 * c) bp (8 * P2Pre.NB 4 lm)
  /-- (`ResSep`) a buffer other than the entry `z` is apart from the stack's current array -/
  rs : 0 < c → 0 < stCap M st → (p = zp ∧ c = zc) ∨ Apart p (8 * c) (stW M st) (8 * stCap M st)

/-- the buffer class: U (`true`) or exactly `zz`'s stack buffer (`false`) -/
@[reducible] def BC (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (zzp bp lm : Nat) (u : Bool) (p c : Nat) : Prop :=
  if u then UB R L K g sp st zp zc M L1 zzp bp lm p c else p = zzp ∧ c = 2 * W lm

/-- the `P2` window step (`z ↦ trunc(trunc(z²)²·powers[d])`, nat.go:1235-1245) -/
@[reducible] def stp (lm X : Nat) : Nat → Nat → Nat :=
  fun z d => Exp.iter (fun z => z * z % 2 ^ lm) 2 z * Exp.p2Pow lm X d % 2 ^ lm

/-- one loop body's budget: two `sqr`s, one `mul`, three `trunc`s (Q-form costs at length `w`) -/
@[reducible] def bc (lm : Nat) : Nat :=
  2 * sqrCQ (W lm) + mulCQ (W lm) (W lm) + 3 * P2Pre.tC lm

/-- the table (`powers[j]`, `j < 4`, headers at `sp + 0x140`, words in `buf`) and `zz`'s stack buffer -/
structure TZ (R : RtInv) (L : List (Nat × Nat)) (m0 M : Memory) (L1 : List (Nat × Nat)) (st sp zzp bp lm X : Nat) :
    Prop where
  pw : ∀ j, j < 4 → P2Pre.PwD M (sp + 0x140) bp lm X j
  bscr : Scr R L L1 m0 M st bp (P2Pre.NB 4 lm)
  bbu : P2Pre.BU M st bp (8 * P2Pre.NB 4 lm)
  zscr : Scr R L L1 m0 M st zzp (2 * W lm)
  zbu : P2Pre.BU M st zzp (8 * (2 * W lm))
  zb : Apart zzp (8 * (2 * W lm)) bp (8 * P2Pre.NB 4 lm)

/-- `TZ` through a step that keeps the stack header, accessibility, the headers `[sp + 0x140, sp + 0x1a0)` and `buf` -/
theorem TZ.keep {R : RtInv} {L : List (Nat × Nat)} {m0 M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {st sp zzp bp lm X : Nat} (h : TZ R L m0 M L1 st sp zzp bp lm X)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hx : LiveExt R L1 L2)
    (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st) (e2 : stCap M' st = stCap M st)
    (hrd : ∀ a k, (sp + 0x140 ≤ a ∧ a + k ≤ sp + 0x1a0) ∨ (bp ≤ a ∧ a + k ≤ bp + 8 * P2Pre.NB 4 lm) →
      M'.readLE a k = M.readLE a k) :
    TZ R L m0 M' L2 st sp zzp bp lm X := by
  refine ⟨fun j hj => ?_, Scr.mono h.bscr hacc hx, ?_, Scr.mono h.zscr hacc hx, ?_, h.zb⟩
  · obtain ⟨d0, d1, d2, d3, d4⟩ := h.pw j hj
    have r0 := hrd (sp + 0x140 + 24 * j) 8 (Or.inl ⟨by omega, by omega⟩)
    have r1 := hrd (sp + 0x140 + 24 * j + 8) 8 (Or.inl ⟨by omega, by omega⟩)
    have r2 := hrd (sp + 0x140 + 24 * j + 16) 8 (Or.inl ⟨by omega, by omega⟩)
    have hjW : (j + 1) * P2Pre.W lm ≤ P2Pre.NB 4 lm := by
      simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
    have hjW' : j * P2Pre.W lm + P2Pre.W lm = (j + 1) * P2Pre.W lm := by rw [Nat.succ_mul]
    have hjj : j * P2Pre.W lm + P2Pre.W lm ≤ P2Pre.NB 4 lm := by rw [hjW']; exact hjW
    rw [← r1] at d2 d3 d4
    refine ⟨r0.trans d0, r2.trans d1, d2, ?_, ?_⟩
    · show M'.readLE _ _ = _
      rw [hrd _ _ (Or.inr ⟨by omega, by omega⟩)]; exact d3
    · rcases Nat.eq_zero_or_pos (M'.readLE (sp + 0x140 + 24 * j + 8) 8) with h0 | h0
      · exact Or.inl h0
      rcases d4 with d4 | d4
      · exact Or.inl d4
      · right; rw [hrd _ _ (Or.inr ⟨by omega, by omega⟩)]; exact d4
  · simp only [P2Pre.BU, e0, e1, e2]; exact h.bbu
  · simp only [P2Pre.BU, e0, e1, e2]; exact h.zbu

/-- the memory facts at the loop test (see the module doc) -/
structure LI (R : RtInv) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 zzp tp kk i : Nat) (u : Bool) (pA lA cA pB lB cB Z : Nat) : Prop where
  wc : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm)
  esl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)
  sc0 : M.readLE (sp + 0xc0) 8 = (BitVec.ofNat 64 kk - 2#64).toNat
  sc8 : M.readLE (sp + 0xc8) 8 = i
  tz : TZ R L s.mem M L1 st sp zzp tp lm (natVal s.mem xp xl)
  la : lA ≤ W lm
  lac : lA ≤ cA
  lbc : lB ≤ cB
  va : natVal M pA lA = Z
  na : NatNorm M pA lA
  ca : BC R L K g sp st zp zc M L1 zzp tp lm u pA cA
  cb : BC R L K g sp st zp zc M L1 zzp tp lm (!u) pB cB
  zo : Z % 2 = 1
  cb0 : 0 < cB

/-- the continuation at the loop test: every state there with `LI`, the register layout, the parity, the budget
`b + (c + 32 i)·bc + tC ≤ b1 + cst` and the model `outerLoop … i yi c Z = FV` reaches `Q` -/
@[reducible] def KL (impl : List Amd64.Segment) (ret0 : W64) (Q : State → Prop) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State) (r5 : W64)
    (zzp tp kk cst FV : Nat) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 i c yi Z pA lA cA pB lB cB : Nat) (u : Bool),
    S.rip = BitVec.ofNat 64 LT → S.regs 4 = BitVec.ofNat 64 sp → S.regs 14 = BitVec.ofNat 64 g → S.regs 5 = r5 →
    S.fsBase = s.fsBase → S.xmm 15 = 0 → S.df = false → S.mem = M →
    S.regs 9 = BitVec.ofNat 64 pA → S.regs 6 = BitVec.ofNat 64 lA → S.regs 12 = BitVec.ofNat 64 cA →
    S.regs 8 = BitVec.ofNat 64 pB → S.regs 1 = BitVec.ofNat 64 lB → S.regs 15 = BitVec.ofNat 64 cB →
    S.regs 3 = BitVec.ofNat 64 yi → S.regs 10 = BitVec.ofNat 64 c - 1#64 → S.regs 13 = BitVec.ofNat 64 st →
    S.regs 7 = BitVec.ofNat 64 yl → S.regs 11 = BitVec.ofNat 64 i → S.regs 2 = BitVec.ofNat 64 yp →
    S.regs 0 = BitVec.ofNat 64 lm →
    LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i u pA lA cA pB lB cB Z →
    i < yl → yi < 2 ^ 64 → c ≤ 32 → (u = true ↔ (c + kk) % 2 = 1) →
    b + (c + 32 * i) * bc lm + P2Pre.tC lm ≤ b1 + cst →
    Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i yi c Z = FV →
    ReachesRet (LibW.program.link impl) ret0 S Q

end FvModexp.Amd64.P2W2
