import FvModexp.Proofs.Arm64.Exp.EvJ14
import FvModexp.Proofs.Arm64.Exp.EvSm
import FvModexp.Proofs.Arm64.Exp.EvTrD

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `z.add(z, u)`'s precondition and frames (agent infra)

* `ZOK.g`, `ZOK.sub`/`ZOK.subL` (the `stepC0` obligations for `z`'s array), `LZ.rd` (`z` as an operand);
* `addPre0`: divmc's `NatAdd.Pre0` at the callee entry (`SP = sp`) for `z.add(z, u)`: `z` = `(pZ, lw, cZ)` (an `LZ`;
  EMPTY `z` is the entry `z` (`Ze`), its window fact from the entry premise `hzw`), `u` a live local;
* `frm_dstZ`: `frm_dst` for the non-stack callee writing `z`'s array (`LZ` destination, possibly empty).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a non-empty `ZOK` array is apart from the `stackguard0` word -/
theorem ZOK.gw (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory} {L1 : List (Nat × Nat)}
    {p c : Nat} (hc : 0 < c) (hz : ZOK R L st zp zc M L1 p c) : Apart p (8 * c) (g + 16) 8 := by
  have hgo : Outside (g + 16) 8 ((sp - K, sp + 448) :: R.rt) := hP.1.2.2.2.2.2.1
  rcases hz with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · exact (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc).2.2.2.2.1.symm
  · simp only [outside_cons] at hgo
    exact (hin.apart hgo.2).symm

theorem ZOK.sub {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat} (h : ZOK R L st zp zc M L1 p c) :
    ∀ a n, Outside a n R.rt → Outside a n (ZS zp zc st s.mem) → Outside a n [(p, p + 8 * c)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · omega
  · have := hin.apart h1; unfold Apart at this; omega

theorem ZOK.subL {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat} (h : ZOK R L st zp zc M L1 p c) :
    ∀ a n, InRanges a n L → Outside a n (ZS zp zc st s.mem) → Outside a n [(p, p + 8 * c)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨-, hap, -⟩
  · omega
  · have := hap.apart_of_inRanges h1; omega

/-- `z` (non-empty) as a callee input at `SP = sp` -/
theorem LZ.rd (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p l c v : Nat}
    (h : LZ R L st zp zc M L1 p l c v) (hc : 0 < c) {S : State} (hsp : S.sp.toNat = sp) (hm : S.mem = M)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 128) : ExpHyp.RdIn R L1 S stk above p l := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨c40, hlv, hz, hlc, -, -⟩ := h
  obtain ⟨-, a2, a3, a4⟩ := hlv hc
  obtain ⟨-, w1, -, -⟩ := ZOK.ap hP hw hc (hz hc)
  unfold Apart at w1
  subst hm
  refine ⟨by omega, Memory.accessible_weaken _ (Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega)), by omega,
    a2.sub (by omega) (by omega), ?_⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.add`'s precondition** (`Pre0`) for `z.add(z, u)` at the callee entry `S'` (`SP = sp`) -/
theorem addPre0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) (hK4 : 4464 ≤ K)
    (hzw : Outside zp (8 * zc) [(sp - K, sp + 448)])
    {S' : State} (fsp : S'.sp = BitVec.ofNat 64 sp) (f28 : S'.regs 28 = BitVec.ofNat 64 g) (fm : S'.mem = M)
    {pZ lw cZ vz pu lu cu vu : Nat} (hz : LZ R L st zp zc M L1 pZ lw cZ vz) (hZe : cZ = 0 → pZ = zp ∧ cZ = zc)
    (hZ64 : pZ < 2 ^ 64) (hu : LN R L s.mem st M L1 pu lu cu vu) (hu64 : pu < 2 ^ 64)
    (huz : 0 < cu → 0 < cZ → Apart pu (8 * cu) pZ (8 * cZ)) (hlw : lw ≤ 2 ^ 12) (hlu : lu ≤ 2 ^ 12)
    (hb : makeCost (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ b1) :
    NatAdd.Pre0 R b1 L1 (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 cZ) (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 lw)
      (BitVec.ofNat 64 cZ) (BitVec.ofNat 64 pu) (BitVec.ofNat 64 lu) (BitVec.ofNat 64 cu) S' := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hsN : S'.sp.toNat = sp := by rw [fsp, BitVec.toNat_ofNat]; have := hP.1.2.2.2.2.2.2.2.2.2.1; omega
  have hgN : (S'.regs 28).toNat = g := by rw [f28, BitVec.toNat_ofNat]; have := hP.1.2.2.1; omega
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hwt : Outside StackNat.wT 16 R.rt := hP.2.2.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) fsp f28 fm (stk := 4464) (above := 80) hK4 (by omega)
  have hcZ := hz.1
  have hcu := hu.1.1
  have hlwc := hz.2.2.2.1
  have hluc := hu.2.1
  have hzwin : Outside pZ (8 * cZ) (win S' 4464 80) := by
    simp only [win, hsN, outside_cons, outside_nil, and_true]
    rcases Nat.eq_zero_or_pos cZ with c0 | c0
    · obtain ⟨e1, e2⟩ := hZe c0
      rw [e1, e2]
      simp only [outside_cons, outside_nil, and_true] at hzw; omega
    · obtain ⟨-, w1, -, -⟩ := ZOK.ap hP hw c0 (hz.2.2.1 c0)
      unfold Apart at w1; omega
  have hx : 0 < lw → M.accessible pZ (8 * lw) false = true ∧ pZ + 8 * lw ≤ 2 ^ 48 ∧ Held R L1 pZ (8 * lw) ∧
      Outside pZ (8 * lw) (win S' 4464 80) := fun hl => by
    have h := LZ.rd hP hw hz (by omega) hsN fm (stk := 4464) (above := 80) hK4 (by omega)
    exact ⟨by rw [← fm]; exact h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hy : 0 < lu → M.accessible pu (8 * lu) false = true ∧ pu + 8 * lu ≤ 2 ^ 48 ∧ Held R L1 pu (8 * lu) ∧
      Outside pu (8 * lu) (win S' 4464 80) := fun hl => by
    have h := LN.rd hP hu (by omega) hsN fm (stk := 4464) (above := 80) hK4 (by omega)
    exact ⟨by rw [← fm]; exact h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  unfold NatAdd.Pre0
  simp only [NatAdd.need, NatAdd.mx]
  rw [LibCalls.tN hZ64, LibCalls.tN (show cZ < 2 ^ 64 by omega), LibCalls.tN (show lw < 2 ^ 64 by omega),
    LibCalls.tN hu64, LibCalls.tN (show lu < 2 ^ 64 by omega), LibCalls.tN (show cu < 2 ^ 64 by omega), hgN, fm]
  refine ⟨hce, hwt, hlwc, hluc, hcZ, hcu, by omega, by omega, hcZ, hz.2.1, hzwin,
    fun hc => ⟨ZOK.gw hP hc (hz.2.2.1 hc), fun _ => by simp, fun hl => Or.inr (apart_shrink (huz (by omega) hc).symm (Nat.mul_le_mul_left 8 hluc))⟩, hx,
    hz.2.2.2.2.2, hu.2.2.2, hy, hw.inv,
    fun _ => ⟨hsv.1 _ _ _ (by unfold makeCap; split <;> split <;> omega), hb⟩,
    fun d src k hk => hsv.2.1 d src k (by omega)⟩

set_option maxRecDepth 20000 in
/-- `frm_dst` for an `LZ` destination (`z`'s array; empty → the destination `(0, 0)`) -/
theorem frm_dstZ (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd ld cd vd : Nat}
    (hd : LZ R L st zp zc M L1 pd ld cd vd) {M' : Memory} {L2 : List (Nat × Nat)} (hx : LiveExt R L1 L2)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 128)
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)]))
    (hLF : LiveFrame M M' L1 [(pd, pd + 8 * cd)]) :
    ∃ qd kd : Nat, (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      Apart qd (8 * kd) (sp - K) (K + 448) ∧
      MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(qd, qd + 8 * kd)] ++ stkWs M st) ∧ StackBackL R L1 L2 st M M' ∧
      (stW M' st = stW M st ∧ stCap M' st = stCap M st) := by
  have hcw := hP.st_cw hstk habove
  rcases Nat.eq_zero_or_pos cd with c0 | c0
  · subst c0
    have hF0 := SubMod2N.memFrame_drop_empty (by omega) hF
    have hL0 : LiveFrame M M' L1 [] :=
      SubMod2N.liveFrame_drop_empty (ws := []) (p := pd) (e := pd + 8 * 0) (by omega)
        (by rw [List.nil_append]; exact hLF)
    have hF1 : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [((0 : Nat), 0 + 8 * 0)]) :=
      hF0.mono fun a n ho => by rw [outside_append] at ho; exact ho.1
    have hL1 : LiveFrame M M' L1 [((0 : Nat), 0 + 8 * 0)] :=
      Expmc.liveFrame_widen hL0 fun _ _ _ => by simp only [outside_nil]
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF1 hL1 hcw out_00
    exact ⟨0, 0, fun _ _ _ _ => out_00, fun _ _ _ _ => out_00, by unfold Apart; omega, f1, f2, f3, f4⟩
  · have hz := hd.2.2.1 c0
    obtain ⟨-, w1, w2, -⟩ := ZOK.ap hP h c0 hz
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF hLF hcw (out1_of_apart w2)
    exact ⟨pd, cd, ZOK.sub hz, ZOK.subL hz, w1, f1, f2, f3, f4⟩

/-- `ResSep` for the entry `z` (copy of `P2W2.rs_z`) -/
theorem rs_zE (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ResSep s.mem M st zp zc := by
  intro hc hn
  rcases hw.kf with h | ⟨hin, hap⟩
  · exact absurd h hn
  · obtain ⟨⟨hzO1, -, -, -⟩, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc
    rcases hzO1 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart at this ⊢; omega
    · exact (hin.apart hO)

end

end FvModexp.Arm64.ExpEven
