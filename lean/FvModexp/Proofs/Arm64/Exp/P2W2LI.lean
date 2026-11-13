import FvModexp.Proofs.Arm64.Exp.P2W2AT

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the loop invariant at the loop test `LT = 0x1b69bc` (agent infra)

Register based (nat.go:1222-1260; the test itself stores `280 := R3`, `112 := R1`): `z = (R3, R1, R14)`,
`zz = (R0, R13, R15)`, `R8 = yi` (shifted), `R7 = c - 1` (signed; `c` windows left in this word), `R4 = kk - 2`
(`oddNumberOfSwaps` = bit 0 clear), `R9 = st`, `R10 = yl`, `R11 = i`, `R12 = yp`, `R2 = lm`; slots `200 = kk - 2`,
`208 = i`.

Buffer classes (`BC u`): `u = true` — the **U-class**: the entry `z` array or a fresh runtime object (`UB`: live,
apart from the window, the stack header / free part, the globals, `zz`'s stack buffer and the table's `buf`);
`u = false` — the **S-class**: exactly `zz`'s stack buffer `(zzp, 2w)`. `z` has class `u`, `zz` class `!u`; every
`sqr`/`mul` writes into `zz`'s buffer (the S buffer is always reused: `2 len ≤ 2w`; a U buffer is reused or
replaced by a fresh one) and swaps, so a body (3 swaps) flips `u`; `u ↔ (c + kk)` odd.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the loop test `0x1b69bc` -/
abbrev LT : Nat := 1796540

/-- the U-class buffer `(p, c)` at memory `M`, live set `L1` (see the module doc) -/
structure UB (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (zzp bp lm p c : Nat) : Prop where
  c40 : c < 2 ^ 40
  live : NatLive M R L1 p c
  org : (p = zp ∧ c = zc) ∨ (0 < c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  ap : 0 < c → Apart p (8 * c) (sp - K) (K + 560) ∧ Apart p (8 * c) st 24 ∧ Apart p (8 * c) RunIface.gA 32 ∧
    Apart p (8 * c) (g + 16) 8 ∧ Apart p (8 * c) (free M st).1 (free M st).2 ∧
    Apart p (8 * c) zzp (8 * (2 * W lm)) ∧ Apart p (8 * c) bp (8 * P2Pre.NB 4 lm)
  /-- (`ResSep`) a buffer other than the entry `z` is apart from the stack's current array -/
  rs : 0 < c → 0 < stCap M st → (p = zp ∧ c = zc) ∨ Apart p (8 * c) (stW M st) (8 * stCap M st)

/-- the buffer class: U (`true`) or exactly `zz`'s stack buffer (`false`) -/
@[reducible] def BC (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (zzp bp lm : Nat) (u : Bool) (p c : Nat) : Prop :=
  if u then UB R L K g sp st zp zc M L1 zzp bp lm p c else p = zzp ∧ c = 2 * W lm

/-- the `P2` window step (`z ↦ trunc(trunc(z²)²·powers[d])`, nat.go:1235-1250) -/
@[reducible] def stp (lm X : Nat) : Nat → Nat → Nat :=
  fun z d => Exp.iter (fun z => z * z % 2 ^ lm) 2 z * Exp.p2Pow lm X d % 2 ^ lm

/-- one loop body's budget: two `sqr`s, one `mul`, three `trunc`s -/
@[reducible] def bc (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ lm : Nat) : Nat :=
  2 * sqC ℓ (W lm) + mlC ℓ (W lm) (W lm) + 3 * P2Pre.tC lm

/-- the table (`powers[j]`, `j < 4`, headers at `sp + 320`, words in `buf`) and `zz`'s stack buffer -/
structure TZ (R : RtInv) (L : List (Nat × Nat)) (m0 M : Memory) (L1 : List (Nat × Nat)) (st sp zzp bp lm X : Nat) :
    Prop where
  pw : ∀ j, j < 4 → P2Pre.PwD M (sp + 320) bp lm X j
  bscr : Scr R L L1 m0 M st bp (P2Pre.NB 4 lm)
  bbu : P2Pre.BU M st bp (8 * P2Pre.NB 4 lm)
  zscr : Scr R L L1 m0 M st zzp (2 * W lm)
  zbu : P2Pre.BU M st zzp (8 * (2 * W lm))
  zb : Apart zzp (8 * (2 * W lm)) bp (8 * P2Pre.NB 4 lm)

/-- `TZ` through a step that keeps the stack header, accessibility, the headers `[sp + 320, sp + 416)` and `buf` -/
theorem TZ.keep {R : RtInv} {L : List (Nat × Nat)} {m0 M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {st sp zzp bp lm X : Nat} (h : TZ R L m0 M L1 st sp zzp bp lm X)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hx : LiveExt R L1 L2)
    (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st) (e2 : stCap M' st = stCap M st)
    (hrd : ∀ a k, (sp + 320 ≤ a ∧ a + k ≤ sp + 416) ∨ (bp ≤ a ∧ a + k ≤ bp + 8 * P2Pre.NB 4 lm) →
      M'.readLE a k = M.readLE a k) :
    TZ R L m0 M' L2 st sp zzp bp lm X := by
  refine ⟨fun j hj => ?_, Scr.mono h.bscr hacc hx, ?_, Scr.mono h.zscr hacc hx, ?_, h.zb⟩
  · obtain ⟨d0, d1, d2, d3, d4⟩ := h.pw j hj
    have r0 := hrd (sp + 320 + 24 * j) 8 (Or.inl ⟨by omega, by omega⟩)
    have r1 := hrd (sp + 320 + 24 * j + 8) 8 (Or.inl ⟨by omega, by omega⟩)
    have r2 := hrd (sp + 320 + 24 * j + 16) 8 (Or.inl ⟨by omega, by omega⟩)
    have hjW : (j + 1) * P2Pre.W lm ≤ P2Pre.NB 4 lm := by
      simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
    have hjW' : j * P2Pre.W lm + P2Pre.W lm = (j + 1) * P2Pre.W lm := by rw [Nat.succ_mul]
    have hjj : j * P2Pre.W lm + P2Pre.W lm ≤ P2Pre.NB 4 lm := by rw [hjW']; exact hjW
    rw [← r1] at d2 d3 d4
    refine ⟨r0.trans d0, r2.trans d1, d2, ?_, ?_⟩
    · show M'.readLE _ _ = _
      rw [hrd _ _ (Or.inr ⟨by omega, by omega⟩)]; exact d3
    · rcases Nat.eq_zero_or_pos (M'.readLE (sp + 320 + 24 * j + 8) 8) with h0 | h0
      · exact Or.inl h0
      rcases d4 with d4 | d4
      · exact Or.inl d4
      · right; rw [hrd _ _ (Or.inr ⟨by omega, by omega⟩)]; exact d4
  · simp only [P2Pre.BU, e0, e1, e2]; exact h.bbu
  · simp only [P2Pre.BU, e0, e1, e2]; exact h.zbu

/-- the memory facts at the loop test (see the module doc) -/
structure LI (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 zzp bp kk i : Nat) (u : Bool) (pA lA cA pB lB cB Z : Nat) : Prop where
  wc : WC R L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm)
  esl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st)
  s200 : M.readLE (sp + 200) 8 = (BitVec.ofNat 64 kk - 2#64).toNat
  s208 : M.readLE (sp + 208) 8 = i
  tz : TZ R L s.mem M L1 st sp zzp bp lm (natVal s.mem xp xl)
  la : lA ≤ W lm
  lac : lA ≤ cA
  lbc : lB ≤ cB
  va : natVal M pA lA = Z
  na : NatNorm M pA lA
  ca : BC R L K g sp st zp zc M L1 zzp bp lm u pA cA
  cb : BC R L K g sp st zp zc M L1 zzp bp lm (!u) pB cB
  zo : Z % 2 = 1
  cb0 : 0 < cB

/-- the continuation at the loop test: every state there with `LI`, the register layout, the parity, the budget
`b + (c + 32 i)·bc + tC ≤ b1 + cst` and the model `outerLoop … i yi c Z = FV` reaches `Q` -/
@[reducible] def KL (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State) (r29 : BitVec 64)
    (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (zzp bp kk cst FV : Nat) : Prop :=
  ∀ (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 i c yi Z pA lA cA pB lB cB : Nat) (u : Bool),
    S.pc = BitVec.ofNat 64 LT → S.sp = BitVec.ofNat 64 sp → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 →
    S.regs 18 = s.regs 18 → S.mem = M →
    S.regs 3 = BitVec.ofNat 64 pA → S.regs 1 = BitVec.ofNat 64 lA → S.regs 14 = BitVec.ofNat 64 cA →
    S.regs 0 = BitVec.ofNat 64 pB → S.regs 13 = BitVec.ofNat 64 lB → S.regs 15 = BitVec.ofNat 64 cB →
    S.regs 8 = BitVec.ofNat 64 yi → S.regs 7 = BitVec.ofNat 64 c - 1#64 → S.regs 4 = BitVec.ofNat 64 kk - 2#64 →
    S.regs 9 = BitVec.ofNat 64 st → S.regs 10 = BitVec.ofNat 64 yl → S.regs 11 = BitVec.ofNat 64 i →
    S.regs 12 = BitVec.ofNat 64 yp → S.regs 2 = BitVec.ofNat 64 lm →
    LI R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp kk i u pA lA cA pB lB cB Z →
    i < yl → yi < 2 ^ 64 → c ≤ 32 → (u = true ↔ (c + kk) % 2 = 1) →
    b + (c + 32 * i) * bc sqC mlC (lvlL (stLen s.mem st) lm) lm + P2Pre.tC lm ≤ b1 + cst →
    Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i yi c Z = FV →
    ReachesRet (LibW.program.link impl) ret0 S Q

end FvModexp.Arm64.P2W2
