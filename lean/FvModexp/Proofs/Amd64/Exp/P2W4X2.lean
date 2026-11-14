import FvModexp.Proofs.Amd64.Exp.P2W4X1
import FvModexp.Proofs.Amd64.Exp.P2W4Cp2

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the exit's `z.set(zz)` copy (agent divmc s77, port of divmc s74; amd64 twin of agent infra's
`Arm64.P2W4X2`)

After an even number of swaps (`kk` even; nat.go:1259-1262) `z` (S-class: `zz`'s stack buffer, `n` words) is copied
into the U-class buffer `(dp, dc)` (`n ≤ dc`; reused or just allocated by `make`). `xJ`: from the join `XJ` =
fn+0x948 (`R8 = dp`, `R9 = zzp`, `SI = AX = n`, `DX = dc`): `CX = min(SI, AX)`, the `R8 == R9` test (refuted: the
buffers are apart), the spills `0x88/0x78/0x120`, `memmove(dp, zzp, 8n)` (return fn+0x97b), the reloads → `nH`
(`nmT`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open FvModexp.Amd64.ExpHyp

/-- the join of the exit's reuse / `make` paths (fn+0x948) -/
abbrev XJ : Nat := 6200328

section
variable {impl : List Amd64.Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the facts after the copy -/
theorem xm (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 ℓ : Nat} (hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {zzp tp X : Nat}
    (htz : TZ R L s.mem M L1 st sp zzp tp lm X) {dp dc n Z : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp tp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n) (hn2 : n ≤ 2 * W lm)
    (hsrc : natVal M zzp n = Z) {M1 m : Memory}
    (hF1 : MemFrame M M1 [(sp + 0x88, sp + 0x90), (sp + 0x78, sp + 0x80), (sp + 0x128, sp + 0x130), (sp - 0x8, sp)])
    (hrg1 : M1.regions = M.regions)
    (hF2 : MemFrame M1 m (R.rt ++ [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 24)] ++ [(dp, dp + 8 * n)]))
    (hLF2 : LiveFrame M1 m L1 [(dp, dp + 8 * n)])
    (hinv2 : R.inv (b1 + stkR (HW (stLen s.mem st) lm) M1 st) L1 g (view R.rt L1 m))
    (hcp : Mem.Copied M1 m dp zzp (8 * n)) (hrg2 : m.regions = M1.regions) :
    WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem m L1 b1 ℓ ∧
      ESl m sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) ∧
      UB R L K g sp st zp zc m L1 zzp tp lm dp dc ∧ natVal m dp n = Z ∧
      (∀ a k, sp + 24 ≤ a → a + k ≤ sp + 0x358 → m.readLE a k = M1.readLE a k) := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  unfold Apart at hstw
  have hdc0 : 0 < dc := by omega
  obtain ⟨hdW, hdH, -, -, -, hdZ, -⟩ := hub.ap hdc0
  have hdW' := hdW
  unfold Apart at hdW'
  have hzW := scr_win hP htz.zscr
  unfold Apart at hzW
  have hdZ' := hdZ
  unfold Apart at hdZ'
  have k1 : ∀ a k, (a + k ≤ sp - 0x8 ∨ (sp ≤ a ∧ a + k ≤ sp + 0x78) ∨ (sp + 0x80 ≤ a ∧ a + k ≤ sp + 0x88) ∨
      (sp + 0x90 ≤ a ∧ a + k ≤ sp + 0x128) ∨ sp + 0x130 ≤ a) → M1.readLE a k = M.readLE a k := fun a k ha =>
    hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hh1 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj => k1 _ _ (by omega)
  have hh2 : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = M1.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF2 hLF2 (by omega) (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
      (by have := hdH; unfold Apart at this ⊢; omega)
  obtain ⟨e10, e11, e12⟩ := hdr3 hh1
  obtain ⟨e20, e21, e22⟩ := hdr3 hh2
  have hw1 := WC.win hP hw hF1 hrg1 (by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [InWN] <;> omega)
  have hw2 := WC.mv hP hw1 hF2 hLF2 hrg2 hinv2 (by have := hdH; unfold Apart at this ⊢; omega)
    (fun a k ho => ?_) (fun a k hin ho => ?_)
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
  have kW : ∀ a k, sp + 24 ≤ a → a + k ≤ sp + 0x358 → m.readLE a k = M1.readLE a k := fun a k h1 h2 =>
    mv_rdW hP hF2 (Or.inr ⟨h1, h2⟩) (by unfold Apart; omega)
  have hacc : ∀ a n w, m.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF1.accessible]
  refine ⟨hw2, ESl.keep hsl (fun a k ha => by rw [kW a k (by omega) (by omega), k1 a k (by omega)]),
    hub.keep hacc (LiveExt.refl R L1) (e20.trans e10) (e21.trans e11) (e22.trans e12), ?_, kW⟩
  show m.readLE dp (8 * n) = Z
  rw [Expmc.readLE_of_copied hcp, k1 _ _ (by omega)]; exact hsrc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the exit's join to the post** -/
theorem xJ (hap : Amd64.ImplApart Extracted.program impl) (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}
    (hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {zzp tp X : Nat}
    (htz : TZ R L s.mem M L1 st sp zzp tp lm X) {dp dc n Z cst : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp tp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n) (hn2 : n ≤ 2 * W lm)
    (hsrc : natVal M zzp n = Z) (hbud : b - cst ≤ b1)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 XJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) (h8 : S.regs 8 = BitVec.ofNat 64 dp) (h9 : S.regs 9 = BitVec.ofNat 64 zzp)
    (h6 : S.regs 6 = BitVec.ofNat 64 n) (h0 : S.regs 0 = BitVec.ofNat 64 n)
    (h2 : S.regs 2 = BitVec.ofNat 64 dc) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b L K zp zc st Z cst s) := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hlm := hP.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hdc0 : 0 < dc := by omega
  have hc40 := hub.c40
  obtain ⟨-, hdH, hdacc, hd48⟩ := hub.live hdc0
  obtain ⟨hdW, -, -, -, -, hdZ, -⟩ := hub.ap hdc0
  have hzs := htz.zscr
  have hzW := scr_win hP hzs
  have hzacc := hzs.acc
  have hz48 := hzs.b48
  unfold Apart at hdW hdZ hzW
  have hne : (BitVec.ofNat 64 dp = BitVec.ofNat 64 zzp) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := (hw.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have hwH : HdM (WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ) := ⟨hw⟩
  have hslH : HdM (ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) := ⟨hsl⟩
  have htzH : HdM (TZ R L s.mem M L1 st sp zzp tp lm X) := ⟨htz⟩
  have hubH : HdM (UB R L K g sp st zp zc M L1 zzp tp lm dp dc) := ⟨hub⟩
  clear hw hsl htz hub hzs
  subst hm
  janus64_run [hne, e8n n (by omega), hwacc, hwaccF] until [mvE]
  have hF1 : MemFrame S.mem ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379) [(sp + 0x88, sp + 0x90), (sp + 0x78, sp + 0x80), (sp + 0x128, sp + 0x130), (sp - 0x8, sp)] := by
    janus_frame
  have hrg1 : ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379).regions = S.mem.regions := by simp only [Janus.Arm64.Memory.regions_writeLE]
  have rpu : ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379).readLE (sp - 0x8) 8 = 6200379 := Janus.Arm64.Memory.readLE_writeLE_self ..
  have r88 : ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379).readLE (sp + 0x88) 8 = dc := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have r78 : ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379).readLE (sp + 0x78) 8 = n := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have r120 : ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379).readLE (sp + 0x128) 8 = dp := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have hw1 := WC.win hP hwH.h hF1 hrg1 (by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [InWN] <;> omega)
  have hra : ((((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379).readLE (sp - 0x8) 8 < 2 ^ 47 := by rw [rpu]; decide
  generalize hM1 : (((S.mem.writeLE (sp + 0x88) 8 dc).writeLE (sp + 0x78) 8 n).writeLE (sp + 0x128) 8 dp).writeLE
      (sp - 0x8) 8 6200379 = M1 at hF1 hrg1 rpu r88 r78 r120 hw1 hra ⊢
  have hzacc1 : M1.accessible zzp (8 * n) false = true := by
    rw [hF1.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hzacc (Nat.le_refl _)
      (by omega))
  refine mvCallW hmv hP hw1 (d := dp) (src := zzp) (n := 8 * n) (by omega) (by omega) (by omega)
    (by omega) hzacc1 (by unfold Apart; omega) (by omega)
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hdacc (Nat.le_refl _) (by omega))
    (hdH.sub (Nat.le_refl _) (by omega)) (by unfold Apart; omega) _ ?_ ?_ ?_ rfl hra ?_ ?_ ?_ ?_ ?_
    (fun junk f x yh m zh kr hF2 hLF2 hinv2 hcp hrg2 => ?_)
  all_goals first | (janus64_simp; done) | skip
  case refine_2 =>
    simp only [setRegF_apply, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  obtain ⟨hw2, hsl2, hub2, hv2, kW⟩ := xm hP hwH.h hslH.h htzH.h hubH.h hnd hn1 hn2 hsrc hF1 hrg1 hF2 hLF2 hinv2 hcp hrg2
  have q88 : m.readLE (sp + 0x88) 8 = dc := by rw [kW _ _ (by omega) (by omega)]; exact r88
  have q78 : m.readLE (sp + 0x78) 8 = n := by rw [kW _ _ (by omega) (by omega)]; exact r78
  have q120 : m.readLE (sp + 0x128) 8 = dp := by rw [kW _ _ (by omega) (by omega)]; exact r120
  have hwacc2 : m.accessible (sp - 0x8 - K) (K + 0x360) true = true := by rw [hF2.accessible, hF1.accessible]; exact hwacc
  have hwaccF2 : m.accessible (sp - 0x8 - K) (K + 0x360) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ hwacc2
  have hwH2 : HdM (WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem m L1 b1 ℓ) := ⟨hw2⟩
  have hslH2 : HdM (ESl m sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) := ⟨hsl2⟩
  have hubH2 : HdM (UB R L K g sp st zp zc m L1 zzp tp lm dp dc) := ⟨hub2⟩
  clear hF1 hM1 r88 r78 r120 hw1 hw2 hsl2 hub2 kW hF2 hLF2 hcp hinv2 hwH hslH htzH hubH
  janus64_run [q88, q78, q120, hwacc2, hwaccF2] until [nH]
  refine nmT hap hP hwH2.h hslH2.h hubH2.h hnd hv2 hbud _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  all_goals first | exact hfs | (janus64_simp; done) | skip
end

end FvModexp.Amd64.P2W4
