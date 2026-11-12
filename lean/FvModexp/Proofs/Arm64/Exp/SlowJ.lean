import FvModexp.Proofs.Arm64.Exp.SlowCP
import FvModexp.Proofs.Arm64.Exp.SlowCalls
import FvModexp.Proofs.Arm64.Exp.SlowCtx

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the loop's shared join facts (ROW-TIME rule: every segment imports this module) (agent expmc)

* `SF … M`: the argument spills (`stk` 464, `x` 472/480/488, `y` 496/504, `m` 520/528/536) and the caller's saved
  FP/LR (`sp - 8`, `sp`), stable from the prologue on (callees keep `[sp - 8, sp + 8)` and `[sp + 120, sp + 544)`);
* `JC … S M L1 b1`: the context at a state `S` (memory `M`, `SP = sp`, `R28 = g`, `R29 = sp - 8`, `R18`, `WC` at the
  entry level, `SF`);
* `BB … M L1 z zl zc Zv zz zzl zzc r rl rc q ql qc`: the four buffers (`z` a live value `Zv`, the others
  destinations with `len ≤ cap`) and their six `Pw` facts;
* `res_norm`: a callee's `NatOF` result whose EMPTY case is its destination's registers, re-pointed so that an empty
  result is `nil`; `rs_of`: `ResSep` from a callee's fresh-result clause.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- the stable slots -/
structure SF (sp st xp xl xc yp yl mp ml mc r29 ret : Nat) (M : Memory) : Prop where
  s464 : M.readLE (sp + 464) 8 = st
  s472 : M.readLE (sp + 472) 8 = xp
  s480 : M.readLE (sp + 480) 8 = xl
  s488 : M.readLE (sp + 488) 8 = xc
  s496 : M.readLE (sp + 496) 8 = yp
  s504 : M.readLE (sp + 504) 8 = yl
  s520 : M.readLE (sp + 520) 8 = mp
  s528 : M.readLE (sp + 528) 8 = ml
  s536 : M.readLE (sp + 536) 8 = mc
  sfp : M.readLE (sp - 8) 8 = r29
  slr : M.readLE sp 8 = ret

theorem SF.keep {sp st xp xl xc yp yl mp ml mc r29 ret : Nat} {M M' : Memory}
    (h : SF sp st xp xl xc yp yl mp ml mc r29 ret M)
    (hk : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 424 ≤ a ∧ a + k ≤ sp + 544) → M'.readLE a k = M.readLE a k) :
    SF sp st xp xl xc yp yl mp ml mc r29 ret M' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a1
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a2
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a3
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a4
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a5
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a6
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a7
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a8
  · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩)]; exact a9
  · rw [hk _ _ (Or.inl ⟨by omega, by omega⟩)]; exact a10
  · rw [hk _ _ (Or.inl ⟨by omega, by omega⟩)]; exact a11

/-- the context at a state of the loop -/
structure JC (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) :
    Prop where
  wc : WC R L K g sp st zp zc s.mem M L1 b1 (stLen s.mem st)
  hm : S.mem = M
  esp : S.sp = BitVec.ofNat 64 sp
  e28 : S.regs 28 = BitVec.ofNat 64 g
  e29 : S.regs 29 = BitVec.ofNat 64 (sp - 8)
  e18 : S.regs 18 = r18
  sf : SF sp st xp xl xc yp yl mp ml mc r29 ret M

/-- the four buffers -/
structure BB (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat) : Prop where
  bz : LN R L st zp zc M L1 z zl zc' Zv
  bzz : DL R L st zp zc M L1 zz zzc
  lzz : zzl ≤ zzc
  br : DL R L st zp zc M L1 r rc
  lr : rl ≤ rc
  bq : DL R L st zp zc M L1 q qc
  lq : ql ≤ qc
  p1 : Pw z zc' zz zzc
  p2 : Pw z zc' r rc
  p3 : Pw z zc' q qc
  p4 : Pw zz zzc r rc
  p5 : Pw zz zzc q qc
  p6 : Pw r rc q qc

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- a destination's pointer and capacity fit a register -/
theorem DL.lt64 {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat}
    (h : DL R L st zp zc M L1 p c) : p < 2 ^ 64 ∧ c < 2 ^ 64 := by
  refine ⟨?_, by have := h.1; omega⟩
  rcases Nat.eq_zero_or_pos c with c0 | c0
  · rw [h.2.2.2.2 c0]; decide
  · have := (h.2.1 c0).2.2.2; omega

/-- `ResSep` from a callee's fresh-result clause -/
theorem rs_of {M M' : Memory} {st pd cd p c : Nat} (hc0 : stCap M' st = 0 → stW M' st = 0)
    (h : ¬ (p = pd ∧ c = cd) → 0 < c → 0 < stCap M' st → Apart p (8 * c) (stW M' st) (8 * stCap M' st)) :
    ¬ (p = pd ∧ c = cd) → ResSep M M' st p c := by
  intro hn hc _
  rcases Nat.eq_zero_or_pos (stCap M' st) with c0 | c0
  · rw [c0, hc0 c0]; unfold Apart; omega
  · exact h hn hc c0

/-- a callee's `NatOF` result re-pointed: an empty result is its destination's registers (`hE`), hence `nil` -/
theorem res_norm {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {pd cd need p' l' c' v : Nat} (hd : DL R L st zp zc M L1 pd cd)
    (hr : ExpHyp.NatOF R L1 L2 M' pd cd need p' l' c' v)
    (hE : c' = 0 → ¬ (p' = pd ∧ c' = cd) → BitVec.ofNat 64 p' = BitVec.ofNat 64 pd ∧ c' = cd) :
    ∃ p'', BitVec.ofNat 64 p'' = BitVec.ofNat 64 p' ∧ ExpHyp.NatOF R L1 L2 M' pd cd need p'' l' c' v ∧
      (c' = 0 → p'' = 0) ∧ (¬ (p'' = pd ∧ c' = cd) → p'' = p') ∧ (0 < c' → p'' = p') := by
  obtain ⟨hv, hn, hlc, hc40, hlv, hof⟩ := hr
  rcases Nat.eq_zero_or_pos c' with c0 | c0
  · subst c0
    have hl0 : l' = 0 := by omega
    subst hl0
    by_cases ho : p' = pd ∧ 0 = cd
    · obtain ⟨rfl, rfl⟩ := ho
      exact ⟨p', rfl, ⟨hv, hn, hlc, hc40, hlv, hof⟩, fun _ => hd.2.2.2.2 rfl, fun hn' => absurd ⟨rfl, rfl⟩ hn',
        fun h => absurd h (Nat.lt_irrefl 0)⟩
    · obtain ⟨e1, e2⟩ := hE rfl ho
      subst e2
      exact ⟨pd, e1.symm, ⟨by rw [← hv]; rfl, Or.inl rfl, Nat.le_refl _, hc40, by simp, Or.inl ⟨rfl, rfl⟩⟩,
        fun _ => hd.2.2.2.2 rfl, fun hn' => absurd ⟨rfl, rfl⟩ hn', fun h => absurd h (Nat.lt_irrefl 0)⟩
  · exact ⟨p', rfl, ⟨hv, hn, hlc, hc40, hlv, hof⟩, fun h => absurd h (by omega), fun _ => rfl, fun _ => rfl⟩

end FvModexp.Arm64.ExpSlow
