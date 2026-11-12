import FvModexp.Proofs.Arm64.Exp.P2W2X1
import FvModexp.Proofs.Arm64.Exp.P2W2Cp3

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the exit's `z.set(zz)` copy (agent infra)

After an odd number of swaps (`oddNumberOfSwaps`, nat.go:1259-1262) `z` (S-class: `zz`'s stack buffer, `n` words)
is copied into the U-class buffer `(dp, dc)` (`n ≤ dc`; reused or just allocated by `make`). `xJ`: from the join
`0x1b6a48` (`R0 = dp`, `R1 = R2 = n`, `R15 = dc`, `R3 = zzp`): `min`, the `dp == zzp` test (refuted: the
buffers are apart), the spills `144/128/288`, `memmove(dp, zzp, 8n)` (return `0x1b6a70`), the reloads → `nmT`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.ExpHyp

/-- the join of the exit's `make` paths -/
abbrev xJE : Nat := 1796680

section
variable {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- the facts after the copy -/
theorem xm (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {ret : Nat}
    (hsl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st)) {zzp bp X : Nat}
    (htz : TZ R L s.mem M L1 st sp zzp bp lm X) {dp dc n Z : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp bp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n)
    (hsrc : NV M zzp n (2 * W lm) Z)
    {M1 m : Memory}
    (hF1 : MemFrame M M1 [(sp + 144, sp + 152), (sp + 128, sp + 136), (sp + 288, sp + 296)])
    (hrg1 : M1.regions = M.regions)
    (hF2 : MemFrame M1 m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(dp, dp + 8 * n)]))
    (hLF2 : LiveFrame M1 m L1 [(dp, dp + 8 * n)]) (hinv2 : R.inv b1 L1 g (view R.rt L1 m))
    (hcp : Mem.Copied M1 m dp zzp (8 * n)) (hrg2 : m.regions = M1.regions) :
    WC R L K g sp st zp zc s.mem m L1 b1 ℓ ∧ ESl m sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st) ∧
      UB R L K g sp st zp zc m L1 zzp bp lm dp dc ∧ NV m dp n dc Z ∧
      (∀ a k, sp + 32 ≤ a → a + k ≤ sp + 560 → m.readLE a k = M1.readLE a k) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hdc0 : 0 < dc := by omega
  obtain ⟨hdW, hdH, -, -, -, hdZ, -⟩ := hub.ap hdc0
  have hdW' := hdW
  unfold Apart at hdW'
  have hzW := scr_win hP htz.zscr
  unfold Apart at hzW
  have hdZ' := hdZ
  unfold Apart at hdZ'
  obtain ⟨hnl, hv, hN, hZo⟩ := hsrc
  have k1 : ∀ a k, (a + k ≤ sp + 128 ∨ sp + 296 ≤ a ∨ (sp + 152 ≤ a ∧ a + k ≤ sp + 288) ∨
      (sp + 136 ≤ a ∧ a + k ≤ sp + 144)) → M1.readLE a k = M.readLE a k := fun a k ha =>
    hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hh1 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj => k1 _ _ (by omega)
  have hh2 : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = M1.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF2 hLF2 (by omega) (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
      (by have := hdH; unfold Apart at this ⊢; omega)
  obtain ⟨e10, e11, e12⟩ := hdr3 hh1
  obtain ⟨e20, e21, e22⟩ := hdr3 hh2
  have hw1 := WC.win hP hw hF1 hrg1 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
  have hw2 := WC.mv hP hw1 hF2 hLF2 hrg2 hinv2 (by have := hdH; unfold Apart at this ⊢; omega) (fun a k ho => ?_)
    (fun a k hin ho => ?_)
  rotate_left
  · rcases hub.org with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · simp only [ZS, outside_append, List.cons_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · rw [outside_append, outside_append] at ho
      have := hin.apart ho.1.1; unfold Apart at this
      simp only [outside_cons, outside_nil, and_true]; omega
  · rcases hub.org with ⟨rfl, rfl⟩ | ⟨-, -, hap⟩
    · simp only [ZS, outside_append, List.cons_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · have := hap.apart_of_inRanges hin
      simp only [outside_cons, outside_nil, and_true]; omega
  have kW : ∀ a k, sp + 32 ≤ a → a + k ≤ sp + 560 → m.readLE a k = M1.readLE a k := fun a k h1 h2 =>
    mv_rdW hP hF2 (Or.inr ⟨h1, h2⟩) (by unfold Apart; omega)
  have kW' : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 32 ≤ a ∧ a + k ≤ sp + 560) →
      (a + k ≤ sp + 128 ∨ sp + 296 ≤ a ∨ (sp + 152 ≤ a ∧ a + k ≤ sp + 288) ∨ (sp + 136 ≤ a ∧ a + k ≤ sp + 144)) →
      m.readLE a k = M.readLE a k := by
    intro a k ha hb
    rw [mv_rdW hP hF2 ha (by unfold Apart; omega), k1 a k (by omega)]
  have hacc : ∀ a n w, m.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF1.accessible]
  have ee0 : stW m st = stW M st := e20.trans e10
  have ee1 : stLen m st = stLen M st := e21.trans e11
  have ee2 : stCap m st = stCap M st := e22.trans e12
  have hsrcB : ∀ j k, j + k ≤ 8 * n → m.readLE (dp + j) k = M.readLE (zzp + j) k := fun j k hjk => by
    rw [Expmc.readLE_of_copied (copied_sub hcp hjk), k1 _ _ (by omega)]
  refine ⟨hw2, ESl.keep hsl (fun a k ha => kW' a k (by omega) (by omega)) (by omega),
    hub.keep hacc (LiveExt.refl R L1) ee0 ee1 ee2, ⟨hnd, ?_, ?_, hZo⟩, kW⟩
  · show m.readLE dp (8 * n) = _
    have := hsrcB 0 (8 * n) (by omega)
    simp only [Nat.add_zero] at this
    rw [this]; exact hv
  · right
    rcases hN with h0 | h0
    · omega
    rw [hsrcB _ _ (by omega)]; exact h0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the exit's join to the post** -/
theorem xJ (hap : ImplApart Extracted.program impl) (hmv : MemmoveLive (LibW.program.link impl) P2Pre.mvE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st (s.regs 29) (s.regs 30).toNat zp zc xp xl xc yp yl lm (stLen s.mem st))
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {zzp bp X : Nat}
    (htz : TZ R L s.mem M L1 st sp zzp bp lm X) {dp dc n Z cst : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp bp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n)
    (hsrc : NV M zzp n (2 * W lm) Z) (hbud : b - cst ≤ b1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xJE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 dp) (h1 : S.regs 1 = BitVec.ofNat 64 n) (h15 : S.regs 15 = BitVec.ofNat 64 dc)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 zzp) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S (FQ R b L K zp zc st Z cst s) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hdc0 : 0 < dc := by omega
  have hc40 := hub.c40
  obtain ⟨-, hdH, hdacc, hd48⟩ := hub.live hdc0
  obtain ⟨hdW, -, -, -, -, hdZ, -⟩ := hub.ap hdc0
  have hzs := htz.zscr
  have hzW := scr_win hP hzs
  have hnl := hsrc.1
  have hzacc := hzs.acc
  have hz48 := hzs.b48
  unfold Apart at hdW hdZ hzW
  have hne : dp ≠ zzp := by intro e; rw [e] at hdZ; omega
  have hlt : ((n : Int) > (n : Int)) = False := by simp
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [hw.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  subst hm
  janus_run [hne, hlt, lsl3, e8n n (by omega), hmacc] until [P2Pre.mvE]
  generalize hM1 : ((S.mem.writeLE (sp + 144) 8 dc).writeLE (sp + 128) 8 n).writeLE (sp + 288) 8 dp = M1
  have hF1 : MemFrame S.mem M1 [(sp + 144, sp + 152), (sp + 128, sp + 136), (sp + 288, sp + 296)] := by
    rw [← hM1]; janus_frame
  have hrg1 : M1.regions = S.mem.regions := by rw [← hM1]; simp only [Memory.regions_writeLE]
  have r144 : M1.readLE (sp + 144) 8 = dc := by
    rw [← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]; omega
  have r128 : M1.readLE (sp + 128) 8 = n := by
    rw [← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]; omega
  have r288 : M1.readLE (sp + 288) 8 = dp := by rw [← hM1, Memory.readLE_writeLE_self]; omega
  have hw1 := WC.win hP hw hF1 hrg1 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
  refine mvCallW hmv _ _ hP hw1 (dst := dp) (src := zzp) (n := 8 * n) (ra := 1796720)
    (by decide) (by decide) (by omega) (by omega)
    (by rw [hF1.accessible]; exact Memory.accessible_mono _ hdacc (Nat.le_refl _) (by omega))
    (hdH.sub (Nat.le_refl _) (by omega)) (by unfold Apart; omega) (by omega)
    (by rw [hF1.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hzacc (Nat.le_refl _)
      (by omega)))
    (by unfold Apart; omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ fun junk f v m ex ep hF2 hLF2 hinv2 hcp hrg2 => ?_
  rotate_left
  all_goals first | (janus_simp; done) | skip
  obtain ⟨hw2, hsl2, hub2, hnv2, kW⟩ := xm hP hw hsl htz hub hnd hn1 hsrc hF1 hrg1 hF2 hLF2 hinv2 hcp hrg2
  have q144 : m.readLE (sp + 144) 8 = dc := by rw [kW _ _ (by omega) (by omega)]; exact r144
  have q128 : m.readLE (sp + 128) 8 = n := by rw [kW _ _ (by omega) (by omega)]; exact r128
  have q288 : m.readLE (sp + 288) 8 = dp := by rw [kW _ _ (by omega) (by omega)]; exact r288
  have hmacc2 : m.accessible (sp - K) (K + 560) true = true := by
    rw [hF2.accessible, hF1.accessible]; exact hmacc
  clear hF1 hM1 r144 r128 r288 hw1 hw hsl hub hsrc htz kW hF2 hLF2 hcp
  janus_run [q144, q128, q288, hmacc2] until [nmE]
  refine nmT hap hP hw2 hsl2 hr4 hr48 hub2 hnv2 hbud _ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W2
