import FvModexp.Proofs.Amd64.NatQ.DivLargeDBP
import FvModexp.Proofs.Amd64.NatQ.DivLargeDRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeDB.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `AtD` after a division callee (pure)

`divPost`: `AtD` from a division callee's post (window `K / A` at the callee entry `RSP - 312`, writes `q[0:m+1]`,
`u`, the stack). `dbPost`: the `divBasic` instance (window `4424 / 88`, budget `stackNatCost`). Port of
`Arm64/Nat/DivLargeDB.lean` (`Mem.glob` is not needed: amd64 reads the threshold in the run, `Mem.thr`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`AtD` after a division callee** (pure): `X` = the callee's entry (memory = `AtJ`'s with `scrB` slots and `q`
written), `T` = after the call (window `K / A`) -/
theorem divPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {dc : Nat → Nat → Nat}
    {zp zc st up uc ip il vp vl : Nat} {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat}
    {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {X : State}
    (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 312)
    (hA : MemFrame S.mem X.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]))
    (hAL : LiveFrame S.mem X.mem Lq [(qp, qp + 8 * qc)])
    (hq0 : X.mem.readLE ((s.regs 4).toNat - 64) 8 = qp) (hq1 : X.mem.readLE ((s.regs 4).toNat - 56) 8 = il - vl + 1)
    (hq2 : X.mem.readLE ((s.regs 4).toNat - 48) 8 = qc) (hreg : X.mem.regions = s.mem.regions)
    {K A : Nat} (hK : K ≤ 40960) (hAb : A ≤ 96)
    {T : State} (hpc : T.rip = BitVec.ofNat 64 joinD) (hTsp : T.regs 4 = s.regs 4 - 304#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hx15 : T.xmm 15 = 0#128) (hdf : T.df = false) (hTreg : T.mem.regions = X.mem.regions)
    (hqv : natVal T.mem qp (il - vl + 1) = natVal X.mem P (il + 1) / natVal X.mem t vl)
    (hrv : natVal T.mem P (il + 1) = natVal X.mem P (il + 1) % natVal X.mem t vl)
    {L' : List (Nat × Nat)} {b' : Nat} (hx : LiveExt R Lq L')
    (hbud : b - (costQ dc il vl + stkR H s.mem st) + stkR H T.mem st ≤ b')
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' T.mem)) (hSB : StackBackL R Lq L' st X.mem T.mem)
    (hMF : MemFrame X.mem T.mem (R.rt ++ win X K A ++ [(qp, qp + 8 * (il - vl + 1)), (P, P + 8 * (il + 1))] ++
      stkWs X.mem st))
    (hLF : LiveFrame X.mem T.mem Lq ([(qp, qp + 8 * (il - vl + 1)), (P, P + 8 * (il + 1))] ++ stkWs X.mem st)) :
    AtD R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L' b'
      (stW T.mem st) (stCap T.mem st) T := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hMU := hS.mem
  have hM := hMU.mem
  have hU := hS.ua
  have hQ := hS.qa
  have hqcap := hQ.cap
  -- reads of held ranges outside `scrB` and `q`
  have rdY : ∀ a n, Held R Lq a n → (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      (a + n ≤ qp ∨ qp + 8 * qc ≤ a) → X.mem.readLE a n = S.mem.readLE a n := by
    intro a n hh hw hq
    rcases hh with hi | ho
    · exact hAL.readLE a n hi (by simp only [outside_cons, outside_nil, and_true]; exact hq)
    · refine hA.readLE a n ?_
      rw [outside_append, outside_append]
      exact ⟨⟨ho, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
        by simp only [outside_cons, outside_nil, and_true]; exact hq⟩
  have hsth := hE.pre.sti.1.2.1
  have hsw := hl.sw
  have hqs := hQ.ps; unfold Apart at hqs
  have hW : stW X.mem st = w1 := by
    simp only [stW]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (Nat.le_refl _) (by omega)))) (by omega) (by omega)]; exact hM.hw
  have hLn : stLen X.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (by omega) (by omega)))) (by omega) (by omega)]; exact hM.hlen
  have hCp : stCap X.mem st = c1 := by
    simp only [stCap]
    rw [rdY _ _ (hS.ext3.held (hE.ext.held (hsth.sub (by omega) (by omega)))) (by omega) (by omega)]; exact hM.hcap
  have hAL' : LiveFrame S.mem X.mem L [(qp, qp + 8 * qc)] :=
    ⟨fun a n hin ho => hAL.readLE a n (hS.ext3.inRanges_old (hE.ext.inRanges_old hin)) ho⟩
  obtain ⟨hf, hlf⟩ := frameX hE hS hspn hA hAL' (K := K) (A := A) (qn := il - vl + 1) hK hAb (by omega) hMF hLF
  obtain ⟨⟨hok, hlen, harr⟩, harrL⟩ := hSB
  have hcb := hok.2.2.2.2.2.2
  -- reads above the callee's window
  have rdT : ∀ a, (s.regs 4).toNat - 200 ≤ a → a + 8 ≤ (s.regs 4).toNat - 40 → T.mem.readLE a 8 = X.mem.readLE a 8 := by
    intro a h1 h2
    refine hMF.readLE a 8 ?_
    have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
    have hqw := hQ.pw; have hpw := hU.pw
    have h1 := (w1_facts hE).2.1
    refine out3 ?_ (by omega) (by have := hU.cap; omega) ?_
    · rw [outside_append]
      exact ⟨hout.of_sub (by omega) (by omega), by simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega⟩
    · simp only [stkWs, hW, hLn, hCp, outside_cons, outside_nil, and_true]; omega
  -- values
  have hvv : natVal X.mem t vl = natVal s.mem vp vl * 2 ^ sh := by
    rw [← hS.vval]; unfold natVal
    exact rdY _ _ (hS.ext3.held hl.theld) (by have := hl.tw; omega) (by have := hQ.pt; unfold Apart at this; omega)
  have huv : natVal X.mem P (il + 1) = natVal s.mem ip il * 2 ^ sh := by
    rw [← hS.uval]; unfold natVal
    have hcap := hU.cap
    exact rdY _ _ (hU.pheld.sub (Nat.le_refl _) (by omega)) (by have := hU.pw; omega)
      (by have := hQ.pu; unfold Apart at this; omega)
  rw [hLn] at hlen
  have hacc : ∀ a n w, T.mem.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hMF.accessible, hA.accessible]
  exact {
    pc := hpc, sp := hTsp, r5 := h5, r14 := h14, fs := hfs, x15 := hx15, df := hdf,
    mem := MemU.frameS hE hMU hU hQ hf hlf rfl (by simp only [stLen] at hlen; exact hlen) rfl hinv,
    sq0 := (rdT _ (by omega) (by omega)).trans hq0,
    sq1 := (rdT _ (by omega) (by omega)).trans hq1,
    sq2 := (rdT _ (by omega) (by omega)).trans hq2,
    ua := hU.frame hacc,
    qa := { hQ with pheld := hx.held hQ.pheld, pacc := by rw [hacc]; exact hQ.pacc },
    ext3 := hS.ext3, ext4 := hx, bud := hbud,
    arr2 := by rw [hW, hCp] at harr; exact harr,
    live2 := hok.2.2.2.2.1, c2len := by have := hok.2.2.2.2.2.1; omega, c2b := hcb, sh63 := hS.sh63,
    qval := by
      rw [hqv, huv, hvv, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)],
    rval := by
      rw [hrv, huv, hvv, Nat.mul_mod_mul_right],
    reg := by rw [hTreg, hreg],
    arrL2 := by
      have h2 : ¬(stW T.mem st = stW X.mem st ∧ stCap T.mem st = stCap X.mem st) →
          (stW T.mem st, stW T.mem st + 8 * stCap T.mem st) ∈ L' ∧ 0 < stCap T.mem st := harrL
      rw [hW, hCp] at h2; exact h2,
    qL := hQ.pheld }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`AtD` after `divBasic`** (pure) -/
theorem dbPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {dc : Nat → Nat → Nat}
    {zp zc st up uc ip il vp vl : Nat} {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat}
    {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {X : State}
    (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 312) (hF : MemFrame S.mem X.mem (callWs s))
    (hq0 : X.mem.readLE ((s.regs 4).toNat - 64) 8 = qp) (hq1 : X.mem.readLE ((s.regs 4).toNat - 56) 8 = il - vl + 1)
    (hq2 : X.mem.readLE ((s.regs 4).toNat - 48) 8 = qc) (hreg : X.mem.regions = s.mem.regions)
    {T : State} (hpc : T.rip = BitVec.ofNat 64 joinD) (hTsp : T.regs 4 = s.regs 4 - 304#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hx15 : T.xmm 15 = 0#128) (hdf : T.df = false) (hTreg : T.mem.regions = X.mem.regions)
    (hqv : natVal T.mem qp (il - vl + 1) = natVal X.mem P (il + 1) / natVal X.mem t vl)
    (hrv : natVal T.mem P (il + 1) = natVal X.mem P (il + 1) % natVal X.mem t vl)
    {L' : List (Nat × Nat)} {b' : Nat} (hx : LiveExt R Lq L')
    (hb : bq - stkR H X.mem st + stkR H T.mem st ≤ b')
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' T.mem)) (hSB : StackBackL R Lq L' st X.mem T.mem)
    (hMF : MemFrame X.mem T.mem (R.rt ++ win X 4424 88 ++ [(qp, qp + 8 * (il - vl + 1)), (P, P + 8 * (il + 1))] ++
      stkWs X.mem st))
    (hLF : LiveFrame X.mem T.mem Lq ([(qp, qp + 8 * (il - vl + 1)), (P, P + 8 * (il + 1))] ++ stkWs X.mem st)) :
    AtD R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L' b'
      (stW T.mem st) (stCap T.mem st) T := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hA : MemFrame S.mem X.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]) := hF.mono fun a n ho => by
    simp only [outside_append] at ho
    have := ho.1.2
    simp only [scrB, callWs, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hAL : LiveFrame S.mem X.mem Lq [(qp, qp + 8 * qc)] := ⟨fun a n hin _ => hF.readLE a n (by
    have hLs := lsep_of hE hS.ext3
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    simp only [callWs, outside_cons, outside_nil, and_true]; omega)⟩
  have hLn : stLen X.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]
    rw [hF.readLE _ _ (by have := hl.sw; simp only [callWs, outside_cons, outside_nil, and_true]; omega)]
    exact hS.mem.mem.hlen
  have hCX : stCap X.mem st = c1 := by
    simp only [stCap]
    rw [hF.readLE _ _ (by have := hl.sw; simp only [callWs, outside_cons, outside_nil, and_true]; omega)]
    exact hS.mem.mem.hcap
  have hbud : b - (costQ dc il vl + stkR H s.mem st) + stkR H T.mem st ≤ b' := by
    have hb3 := hS.bud3
    have hb1 := hE.bud
    have hc := hE.pre.cost
    simp only [stkR] at hb hb1 hc ⊢
    rw [hCX] at hb
    simp only [costQ] at hc ⊢
    omega
  exact divPost hE hS hspn hA hAL hq0 hq1 hq2 hreg (K := 4424) (A := 88) (by omega) (by omega) hpc hTsp h5 h14 hfs
    hx15 hdf hTreg hqv hrv hx hbud hinv hSB hMF hLF

end FvModexp.Amd64.Q.DivLarge
