import FvModexp.Proofs.Arm64.Exp.SubMod2NGL

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: callee preconditions (`trunc`, empty-tolerant `sub`, `add`), the `nat.sub`
call helper on `SubHypR0`, and the postcondition (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
/-- the precondition of a `trunc` call at `SP - 144`: destination `z'` given by its facts, budget base `bb ≥ cost n`,
at most `k ≤ 4` budgeted calls before -/
theorem truncPreG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {stk above : Nat} (hkT : stk ≤ 4464) (haT : above ≤ 88)
    {zp' zl' zc' : Nat} (hzl' : zl' ≤ zc') (hzc' : zc' < 2 ^ 40) (hzlv : NatLive M R L1 zp' zc')
    (hzw' : 0 < zc' → (zp' + 8 * zc' ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zp') ∧
      Apart zp' (8 * zc') ((s.regs 28).toNat + 16) 8)
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ x) (hxl : xl ≤ 2 ^ 16)
    (halias : zp' = x ∨ (0 < zc' → 0 < xl → Apart zp' (8 * zc') x (8 * xl))) :
    TruncPre R b1 L1 stk above zp' zl' zc' x xl n S := by
  have hce := CallW.callEnv_of (cenvG_of hpre hrt (dlG_of hpre hrt)) hsp (h28.trans (Expmc.bv_ofNat_toNat _).symm)
    hS hkT haT
  have hsp4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hn15 := hpre.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, -⟩ := hrt
  refine ⟨hce, hpre.2.1, hzl', ⟨hzc', by rw [hS]; exact hzlv, fun hc => ?_⟩, ⟨hx40, by rw [hS]; exact hxa, hx48, hxh, ?_⟩,
    hxl, by omega, halias, ?_, by rw [hS, h28]; exact hinv⟩
  · obtain ⟨h1, h2⟩ := hzw' hc
    simp only [win, hspT, h28, outside_cons, outside_nil, and_true]
    exact ⟨by omega, h2⟩
  · simp only [win, hspT, outside_cons, outside_nil, and_true]; omega
  · have h1 := truncNeed_le_w xl n
    simp only [cost] at hbb
    rw [Nat.mul_comm] at hbud
    have h2 : wCost n * k ≤ wCost n * 4 := Nat.mul_le_mul_left _ hk
    omega


theorem PreG.costB {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) : cost n ≤ b :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1

theorem PreG.zwin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) :
    (zp + 8 * zc ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zp) ∧ Apart zp (8 * zc) ((s.regs 28).toNat + 16) 8 := by
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw
  exact ⟨hzw, hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- `truncPreG_of` with `z` itself as the destination -/
theorem truncPreG_self {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {stk above : Nat} (hkT : stk ≤ 4464) (haT : above ≤ 88) {zl' : Nat} (hzl' : zl' ≤ zc)
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ x) (hxl : xl ≤ 2 ^ 16)
    (halias : zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) :
    TruncPre R b1 L1 stk above zp zl' zc x xl n S :=
  truncPreG_of hpre hbb hrt hk hS hsp h28 hkT haT hzl' hpre.2.2.2.2.2.2.2.2.2.2.1 hrt.2.2.2.2.2.2
    (fun _ => hpre.zwin) hx40 hxa hx48 hxh hxw hxl halias

/-- `truncPreG_of` with a `nil` destination -/
theorem truncPreG_nil {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {stk above : Nat} (hkT : stk ≤ 4464) (haT : above ≤ 88)
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ x) (hxl : xl ≤ 2 ^ 16) :
    TruncPre R b1 L1 stk above 0 0 0 x xl n S :=
  truncPreG_of hpre hbb hrt hk hS hsp h28 hkT haT (Nat.le_refl _) (by decide) (by simp)
    (fun h => absurd h (by decide)) hx40 hxa hx48 hxh hxw hxl (Or.inr fun h => absurd h (by decide))

set_option maxRecDepth 20000 in
/-- the precondition of `z.sub(x, y)` at `SP - 144` (empty-tolerant operands; `z` = the entry `z`, at most two
budgeted calls before) -/
theorem subPre0_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ 2) {S : State} (hS : S.mem = M)
    (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {xp xl xc yp' yl' yc' : Nat} (hyx : yl' ≤ xl) (hYX : natVal M yp' yl' ≤ natVal M xp xl) (hxc : xl ≤ xc)
    (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40) (hxW : xl ≤ W n) (hxp : xp < 2 ^ 64)
    (hyp : yp' < 2 ^ 64)
    (hzx : 0 < zc → 0 < xl → zp = xp ∨ Apart zp (8 * zc) xp (8 * xl))
    (hzy : 0 < zc → 0 < yl' → zp = yp' ∨ Apart zp (8 * zc) yp' (8 * yl'))
    (hx : 0 < xl → M.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧ Held R L1 xp (8 * xl) ∧
      (xp + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ xp)) (hxn : NatNorm M xp xl)
    (hy : 0 < yl' → M.accessible yp' (8 * yl') false = true ∧ yp' + 8 * yl' ≤ 2 ^ 48 ∧ Held R L1 yp' (8 * yl') ∧
      (yp' + 8 * yl' ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ yp')) (hyn : NatNorm M yp' yl') :
    SubPre0 R b1 L1 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hce := CallW.callEnv_of (cenvG_of hpre hrt (dlG_of hpre hrt)) hsp (h28.trans (Expmc.bv_ofNat_toNat _).symm) hS
    (show 4304 ≤ 4464 by omega) (show 80 ≤ 88 by omega)
  have hsp4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hz64 := hpre.2.2.2.2.2.2.2.2.2.1.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  have hserv := hpre.2.1
  have hwt := hpre.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, hlive⟩ := hrt
  have hmk : makeCost xl ≤ wCost n := makeCost_le_w (by omega)
  simp only [cost] at hcost
  have hkw : k * wCost n ≤ 2 * wCost n := Nat.mul_le_mul_right _ hk
  simp only [W] at hxW
  unfold SubPre0
  rw [tN hz64, tN (show zc < 2 ^ 64 by omega), tN hxp, tN (show xl < 2 ^ 64 by omega),
    tN (show xc < 2 ^ 64 by omega), tN hyp, tN (show yl' < 2 ^ 64 by omega), tN (show yc' < 2 ^ 64 by omega), hS]
  simp only [win, hspT, h28, K, A, outside_cons, outside_nil, and_true] at hzw ⊢
  refine ⟨hce, hwt, hyx, hYX, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc, hlive, fun _ => by omega,
    fun hz => ⟨by unfold Apart at hzg ⊢; omega, fun h => ?_, fun h => ?_⟩, fun h => ?_, hxn, hyn, fun h => ?_, hinv,
    fun _ => ⟨hserv.1 _ _ _ (by unfold makeCap; split <;> omega), by omega⟩,
    fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx hz h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy hz h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · obtain ⟨a1, a2, a3, a4⟩ := hx h
    exact ⟨a1, a2, a3, by omega⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hy h
    exact ⟨a1, a2, a3, by omega⟩

set_option maxRecDepth 20000 in
/-- the precondition of `z.add(x, y)` at `SP - 144`: destination `z'` given by its facts, budget base `bb ≥ cost n`,
at most `k ≤ 4` budgeted calls before -/
theorem addPreG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {zp' zc' : Nat} (hc0 : 0 < zc') (hzc' : zc' < 2 ^ 40) (hzlv : NatLive M R L1 zp' zc') (hz64 : zp' < 2 ^ 64)
    (hzw' : 0 < zc' → (zp' + 8 * zc' ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zp') ∧
      Apart zp' (8 * zc') ((s.regs 28).toNat + 16) 8)
    {xp xl xc yp' yl' yc' : Nat} (hxc : xl ≤ xc) (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40)
    (hxW : xl ≤ W n) (hyW : yl' ≤ W n)
    (hzx : zp' = xp ∨ Apart zp' (8 * zc') xp (8 * xl)) (hzy : zp' = yp' ∨ Apart zp' (8 * zc') yp' (8 * yl'))
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxh : Held R L1 xp (8 * xl))
    (hxn : NatNorm M xp xl) (hxw : xp + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ xp)
    (hya : M.accessible yp' (8 * yl') false = true) (hy48 : yp' + 8 * yl' ≤ 2 ^ 48) (hyh : Held R L1 yp' (8 * yl'))
    (hyn : NatNorm M yp' yl') (hyw : yp' + 8 * yl' ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ yp') :
    NatAdd.Pre R b1 L1 (BitVec.ofNat 64 zp') (BitVec.ofNat 64 zc') (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hce := CallW.callEnv_of (cenvG_of hpre hrt (dlG_of hpre hrt)) hsp (h28.trans (Expmc.bv_ofNat_toNat _).symm) hS
    (show 4464 ≤ 4464 by omega) (show 80 ≤ 88 by omega)
  have hsp4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hn2 := hpre.2.2.2.2.2.2.2.1
  have hserv := hpre.2.1
  have hwt := hpre.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, -⟩ := hrt
  have hmk : makeCost (if min xl yl' = 0 then max xl yl' else max xl yl' + 1) ≤ wCost n :=
    makeCost_le_w (by split <;> omega)
  simp only [W] at hxW hyW
  simp only [cost] at hbb
  have hkw : k * wCost n ≤ 4 * wCost n := Nat.mul_le_mul_right _ hk
  have hxp : xp < 2 ^ 64 := by omega
  have hyp : yp' < 2 ^ 64 := by omega
  unfold NatAdd.Pre NatAdd.PreS
  simp only [NatAdd.need, NatAdd.mx]
  rw [tN hz64, tN (show zc' < 2 ^ 64 by omega), tN hxp, tN (show xl < 2 ^ 64 by omega),
    tN (show xc < 2 ^ 64 by omega), tN hyp, tN (show yl' < 2 ^ 64 by omega), tN (show yc' < 2 ^ 64 by omega), hS]
  simp only [win, hspT, h28, K, A, outside_cons, outside_nil, and_true]
  refine ⟨hce, hwt, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc', hzlv, ?_,
    fun hc => ⟨by have := (hzw' hc).2; unfold Apart at this ⊢; omega, ?_, ?_⟩, hxa, hx48, hxh, hxn, hyn, by omega, hya,
    hy48, hyh, by omega, hinv,
    fun _ => ⟨hserv.1 _ _ _ (by unfold makeCap; split <;> split <;> omega), by omega⟩,
    fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · have := (hzw' hc0).1; omega
  · rcases hzx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h

set_option maxRecDepth 20000 in
/-- a call of `nat.sub` (premise `SubHypR0`) at its entry `1781872` with `SP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem subCall0 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} (hsub : SubHypR0 impl R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat} {M : Memory}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatSub.names).link impl) ra) (bra : ra < 2 ^ 64)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' < 2 ^ 64) (bx39 : xl < 2 ^ 39)
    (hpc : S.pc = BitVec.ofNat 64 1781872) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 xp) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 sp') (h28 : (S.regs 28).toNat = g)
    (hpre : SubPre0 R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.pc = BitVec.ofNat 64 ra →
      s'.sp = BitVec.ofNat 64 sp' → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 → s'.regs 18 = S.regs 18 →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl - natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ xl → LiveExt R L L' → b - makeCost xl ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4304, sp' - 8), (sp' + 8, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] → (xl ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS' := CallWW.hypSum hap sub_names (hsub b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatSub.fn = 1781872 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  · obtain ⟨p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    have hspT : S.sp.toNat = sp' := by rw [hsp]; exact tN bsp
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [winA, hspT, h28] at hF hinv
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (hr.trans h30) (e1.trans hsp) e2 e3 e4 hrg (by rw [← q0, Expmc.bv_ofNat_toNat])
      (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat]) hv hn hlc hln hLE hb hinv hlive hor
      hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 bx39)
    obtain ⟨a1, a2⟩ := hr1 h
    exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

/-- the general postcondition from the runtime facts after the last call (relative to `b - g · gA n`) and the result -/
theorem post_ofG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n k g : Nat} {s s' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat} (hrt : Rt R (b - g * gA n) L s zp zc n k s'.mem L2 b2) (hk : k ≤ 5)
    (hg : g ≤ W n) (hg0 : W n ≤ zc → g = 0)
    {p' l' c' : Nat} (e0 : (s'.regs 0).toNat = p') (e1 : (s'.regs 1).toNat = l') (e2 : (s'.regs 2).toNat = c')
    (hv : natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n) (hnorm : NatNorm s'.mem p' l')
    (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40) (hlive : NatLive s'.mem R L2 p' c')
    (hor : (p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hre : W n + 1 ≤ zc → p' = zp ∧ c' = zc) :
    PostG R b L zp zl zc yp yl n s s' := by
  obtain ⟨-, hF, hLF, hLE, hb, hinv, -⟩ := hrt
  have h1 : k * wCost n ≤ 5 * wCost n := Nat.mul_le_mul_right _ hk
  have h2 : g * gA n ≤ W n * gA n := Nat.mul_le_mul_right _ hg
  refine ⟨p', l', c', e0, e1, e2, hv, hnorm, hlc, hc40, L2, b2, hLE, by simp only [costG, cost]; omega, fun hW => ?_,
    hinv, hlive, hor, hF, hLF, hre⟩
  rw [hg0 hW, Nat.zero_mul, Nat.sub_zero] at hb
  simp only [cost]; omega

/-- `post_ofG` without growth (runtime facts relative to `b`) -/
theorem post_ofG0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n k : Nat} {s s' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat} (hrt : Rt R b L s zp zc n k s'.mem L2 b2) (hk : k ≤ 5)
    {p' l' c' : Nat} (e0 : (s'.regs 0).toNat = p') (e1 : (s'.regs 1).toNat = l') (e2 : (s'.regs 2).toNat = c')
    (hv : natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n) (hnorm : NatNorm s'.mem p' l')
    (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40) (hlive : NatLive s'.mem R L2 p' c')
    (hor : (p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hre : W n + 1 ≤ zc → p' = zp ∧ c' = zc) :
    PostG R b L zp zl zc yp yl n s s' := by
  obtain ⟨-, hF, hLF, hLE, hb, hinv, -⟩ := hrt
  have h1 : k * wCost n ≤ 5 * wCost n := Nat.mul_le_mul_right _ hk
  exact ⟨p', l', c', e0, e1, e2, hv, hnorm, hlc, hc40, L2, b2, hLE, by simp only [costG, cost]; omega,
    fun _ => by simp only [cost]; omega, hinv, hlive, hor, hF, hLF, hre⟩

theorem sp_ret {x : BitVec 64} (h : 144 ≤ x.toNat) : BitVec.ofNat 64 (x.toNat - 144) + 144#64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

end FvModexp.Arm64.SubMod2N
