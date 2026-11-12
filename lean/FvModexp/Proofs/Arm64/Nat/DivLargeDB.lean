import FvModexp.Proofs.Arm64.Nat.DivLargeDBP
import FvModexp.Proofs.Arm64.Nat.DivLargeDRel

/-!
# `divLarge` (arm64): `n < divRecursiveThreshold` → `q.divBasic(stk, u, v)` (natdiv.go:626-627), `joinQ` → `joinD`

`Mem.glob`: the threshold globals are unchanged since the entry. `dbPost` (pure): `AtD` from `divBasic`'s post.
`db2`: at `divBasic`'s entry, the call. `db`: from `joinQ` (q slots stored, threshold load, `BLT`) to the call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- the threshold globals keep their values (pure) -/
theorem Mem.glob {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hM : Mem R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk M) :
    M.readLE 7147136 8 = 40 ∧ M.accessible 7147136 8 false = true := by
  have hpre := hE.pre
  have hgl := hpre.gl
  have eg : RunIface.gA = 7147136 := rfl
  obtain ⟨-, -, -, h40, -, -, -, hacc, hrt, hw, -⟩ := hgl
  have hga := hpre.ga
  replace h40 : s.mem.readLE 7147136 8 = 40 := h40
  rw [eg] at hacc hrt hw hga
  obtain ⟨hz, hu, hs, hf⟩ := hga
  simp only [win, outside_cons, outside_nil, and_true] at hw
  refine ⟨?_, by rw [hM.fr.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)⟩
  rw [hM.fr.readLE _ _ ?_]; exact h40
  have hlc := hpre.sti.1.2.2.2.2.2.1
  simp only [outside_append]
  refine ⟨⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [winA, outside_cons, outside_nil, and_true]; omega
  · refine outside_wsL ?_ (fun h => by have := hz h; unfold Apart at this; omega)
      (fun h => by have := hu h; unfold Apart at this; omega)
    rcases hE.scr.loc with ⟨-, h1, h2⟩ | ⟨hin, -⟩
    · unfold Apart at hf; omega
    · have := outside_of_inRanges hrt hin; omega
  · unfold Apart at hs hf
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`AtD` after `divBasic`** (pure) -/
theorem dbPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {dc : Nat → Nat → Nat → Nat}
    {zp zc st up uc ip il ic vp vl vc : Nat} {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat}
    {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {X : State}
    (hsp : X.sp = s.sp - 304#64) (hF : MemFrame S.mem X.mem [(s.sp.toNat - 64, s.sp.toNat - 40)])
    (hq0 : X.mem.readLE (s.sp.toNat - 64) 8 = qp) (hq1 : X.mem.readLE (s.sp.toNat - 56) 8 = il - vl + 1)
    (hq2 : X.mem.readLE (s.sp.toNat - 48) 8 = qc) (hreg : X.mem.regions = s.mem.regions)
    {T : State} (hpc : T.pc = BitVec.ofNat 64 joinD) (hTsp : T.sp = s.sp - 304#64) (h28 : T.regs 28 = s.regs 28)
    (h29 : T.regs 29 = s.sp - 312#64) (h18 : T.regs 18 = s.regs 18) (hTreg : T.mem.regions = X.mem.regions)
    (hqv : natVal T.mem qp (il - vl + 1) = natVal X.mem P (il + 1) / natVal X.mem t vl)
    (hrv : natVal T.mem P (il + 1) = natVal X.mem P (il + 1) % natVal X.mem t vl)
    {L' : List (Nat × Nat)} {b' : Nat} (hx : LiveExt R Lq L')
    (hb : bq - stackNatCost (stLen X.mem st) (vl + 1) ≤ b')
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' T.mem)) (hSB : StackBack R Lq L' st X.mem T.mem)
    (hMF : MemFrame X.mem T.mem (R.rt ++ winA X 4464 88 ++ [(qp, qp + 8 * (il - vl + 1)), (P, P + 8 * (il + 1))] ++
      stkWs X.mem st))
    (hLF : LiveFrame X.mem T.mem Lq ([(qp, qp + 8 * (il - vl + 1)), (P, P + 8 * (il + 1))] ++ stkWs X.mem st)) :
    AtD R b L (cost dc (stLen s.mem st) il vl) zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L' b'
      (stW T.mem st) (stCap T.mem st) T := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2
  have hspn : X.sp.toNat = s.sp.toNat - 304 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hMU := hS.mem
  have hM := hMU.mem
  have hU := hS.ua
  have hQ := hS.qa
  have hqcap := hQ.cap
  have rdX : ∀ a n, a + n ≤ s.sp.toNat - 64 ∨ s.sp.toNat - 40 ≤ a → X.mem.readLE a n = S.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact h)
  have hW : stW X.mem st = w1 := by
    simp only [stW]; rw [rdX _ _ (by have := hl.sw; omega)]; exact hM.hw
  have hLn : stLen X.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]; rw [rdX _ _ (by have := hl.sw; omega)]; exact hM.hlen
  have hCp : stCap X.mem st = c1 := by
    simp only [stCap]; rw [rdX _ _ (by have := hl.sw; omega)]; exact hM.hcap
  -- frames
  have hA : MemFrame S.mem X.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]) := hF.mono fun a n ho => by
    simp only [outside_append] at ho
    have := ho.1.2
    simp only [scrB, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hAL : LiveFrame S.mem X.mem L [(qp, qp + 8 * qc)] := ⟨fun a n hin _ => hF.readLE a n (by
    have hLs := hl.lsep
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r (hE.ext.mem_old hr)
    simp only [outside_cons, outside_nil, and_true]; omega)⟩
  obtain ⟨hf, hlf⟩ := frameX hE hS hspn hA hAL (K := 4464) (A := 88) (qn := il - vl + 1) (by omega) (by omega)
    (by omega) hMF hLF
  obtain ⟨hok, hlen, harr⟩ := hSB
  have hsl := hok.2.2.2.2.2.1
  have hcb := hok.2.2.2.2.2.2
  -- reads above the callee's window
  have rdT : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat - 40 → T.mem.readLE a 8 = X.mem.readLE a 8 := by
    intro a h1 h2
    refine hMF.readLE a 8 ?_
    have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
    have hqw := hQ.pw; have hpw := hU.pw
    have hsw := hl.sw
    have h1 := (w1_facts hE).2.1
    refine out3 ?_ (by omega) (by have := hU.cap; omega) ?_
    · rw [outside_append]
      exact ⟨hout.of_sub (by omega) (by omega), by simp only [winA, outside_cons, outside_nil, and_true]; rw [hspn]; omega⟩
    · simp only [stkWs, hW, hLn, hCp, outside_cons, outside_nil, and_true]; omega
  -- values
  have hvv : natVal X.mem t vl = natVal s.mem vp vl * 2 ^ sh := by
    rw [← hS.vval]; unfold natVal; exact rdX _ _ (by have := hl.tw; omega)
  have huv : natVal X.mem P (il + 1) = natVal s.mem ip il * 2 ^ sh := by
    rw [← hS.uval]; unfold natVal; exact rdX _ _ (by have := hU.pw; omega)
  have hb3 := hS.bud3
  have hb1 := hE.bud
  have hc := hE.pre.cost
  rw [hLn] at hb hlen
  simp only [cost] at hc
  have hacc : ∀ a n w, T.mem.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hMF.accessible, hF.accessible]
  exact {
    pc := hpc, sp := hTsp, r28 := h28, r29 := h29, r18 := h18,
    mem := MemU.frameS hE hMU hU hQ hf hlf rfl (by simp only [stLen] at hlen; exact hlen) rfl hinv,
    sq0 := (rdT _ (by omega) (by omega)).trans hq0,
    sq1 := (rdT _ (by omega) (by omega)).trans hq1,
    sq2 := (rdT _ (by omega) (by omega)).trans hq2,
    ua := (hU.live hx).frame hacc,
    qa := { hQ with pheld := hx.held hQ.pheld, pacc := by rw [hacc]; exact hQ.pacc },
    ext3 := hS.ext3, ext4 := hx, bud := by simp only [cost]; omega,
    arr2 := by rw [hW, hCp] at harr; exact harr,
    live2 := hok.2.2.2.2.1, c2len := by omega, c2b := hcb, sh63 := hS.sh63,
    qval := by
      rw [hqv, huv, hvv, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)],
    rval := by
      rw [hrv, huv, hvv, Nat.mul_mod_mul_right],
    reg := by rw [hTreg, hreg] }

end FvModexp.Arm64.DivLarge
