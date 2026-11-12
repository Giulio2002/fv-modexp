import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W2PowDefs

/-!
# window-2 prologue (arm64): the table loop (nat.go:1415-1417), `i = 2 … 3`

`powers[i] = buf[i·n:(i+1)·n:(i+2)·n].montgomery(powers[i-1], powers[1], m, k0, numWords)`; induction on `4 - i`
from the loop head (`CMP $4, R0`) to the exit `j4`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf mcall_of)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- one table step `i → i + 1` (`2 ≤ i < 4`) -/
theorem powStep (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 bp bc : Nat) (M0 : Memory) (r18 r29 : BitVec 64)
    (tbl : Nat → Nat) (hs : PStatic R L g sp n mp mc k0 bp bc M0)
    (i : Nat) (S : State) (M : Memory) (hi2 : 2 ≤ i) (hi : i < 4)
    (hpc : S.pc = BitVec.ofNat 64 powHead) (hsp : S.sp = BitVec.ofNat 64 sp) (h0 : S.regs 0 = BitVec.ofNat 64 i)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (hF : FP R L sp bp bc M0 M) (hinv : R.inv b L g (view R.rt L M)) (hrg : M.regions = M0.regions)
    (hE : ∀ d, d < i → Ent sp n bp tbl M d)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 powHead → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 (i + 1) → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 →
      S'.mem = M' → FP R L sp bp bc M0 M' → R.inv b L g (view R.rt L M') → M'.regions = M0.regions →
      (∀ d, d < i → Ent sp n bp tbl M' d) →
      Ent sp n bp (fun _ => Exp.montgomery n (tbl (i - 1)) (tbl 1) (M0.readLE mp (8 * n)) k0) M' i →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have hs' := hs
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hm, hbc, hbc', hba, hbb, hbh, hbw, hbg, hbm, r728, r736, r744, r224, r128,
    r248, r536, hok⟩ := hs'
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have he' : Env R L g sp M0 := ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩
  -- products as the executor computes them
  have hin1 : (i + 1) * n = i * n + n := Nat.succ_mul i n
  have hin2 : (i + 2) * n = i * n + 2 * n := by rw [Nat.add_mul]
  have hin0 : (i - 1) * n + n = i * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hin16 : i * n + 2 * n ≤ 5 * n := by
    have := Nat.mul_le_mul_right n (show i + 2 ≤ 5 by omega); rw [Nat.add_mul] at this; omega
  have hin3 : 2 * n ≤ i * n := Nat.mul_le_mul_right n hi2
  have hrB := buf_sub hs (d := i) (by omega)
  have hxI := inp_ent hs (d := i - 1) (by omega)
  have hyI := inp_ent hs (d := 1) (by omega)
  have hA := LibWC.montSum impl hap R hclr hmv b L g sp n mp mc (bp + 8 * (i * n)) (2 * n) (bp + 8 * ((i - 1) * n))
    (bp + 8 * (1 * n)) k0 (BitVec.ofNat 64 n) (BitVec.ofNat 64 (2 * n)) (BitVec.ofNat 64 (2 * n)) (M0.readLE (g + 16) 8)
    (mcall_of he' hn hmc hmc' hrB hxI hyI hm (by unfold Apart; omega) (by unfold Apart; omega)
      (by have := hbm; unfold Apart at this ⊢; omega) (hok _)) hk0
  -- frame-slot reads at `M`
  have rd : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 320 ∨ (sp + 336 ≤ a ∧ a + 8 ≤ sp + 432) ∨
      (sp + 528 ≤ a ∧ a + 8 ≤ sp + 592) ∨ (sp + 600 ≤ a ∧ a + 8 ≤ sp + 752) → M.readLE a 8 = M0.readLE a 8 := by
    intro a h1 h2
    refine hF.1.readLE _ _ ?_
    have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
    have := hbw; unfold Apart at this
    simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
    omega
  have m1016 : M.readLE (sp + 728) 8 = mp := by rw [rd _ (by omega) (by omega)]; exact r728
  have m1024 : M.readLE (sp + 736) 8 = n := by rw [rd _ (by omega) (by omega)]; exact r736
  have m1032 : M.readLE (sp + 744) 8 = mc := by rw [rd _ (by omega) (by omega)]; exact r744
  have m224 : M.readLE (sp + 224) 8 = k0 := by rw [rd _ (by omega) (by omega)]; exact r224
  have m128 : M.readLE (sp + 128) 8 = 2 * n := by rw [rd _ (by omega) (by omega)]; exact r128
  have m248 : M.readLE (sp + 248) 8 = bc := by rw [rd _ (by omega) (by omega)]; exact r248
  have m824 : M.readLE (sp + 536) 8 = bp := by rw [rd _ (by omega) (by omega)]; exact r536
  obtain ⟨-, e1p, e1l, e1c⟩ := hE 1 (by omega)
  obtain ⟨-, ep, el, ec⟩ := hE (i - 1) (by omega)
  have hgM : M.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine hF.1.readLE _ _ ?_
    have h1 := hgw; have h2 := hbg
    unfold Apart at h1 h2
    simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true, hgrt, true_and]
    omega
  have hF0 := hF
  obtain ⟨hFm, hLF⟩ := hF
  simp only [pl, pw, List.append_assoc, List.cons_append, List.nil_append] at hFm
  have hrA := hrB.2.2.1
  have hxA := hxI.1
  have hyA := hyI.1
  have hmA := hm.1
  have h16 : ¬ (4 ≤ i) := by omega
  have mw2 := mulw n i 2 hn16 hi (by decide)
  have mw1 := mulw n i 1 hn16 hi (by decide)
  have mw0 := mulw0 n i hn16 hi
  janus_run [m1016, m1024, m1032, m224, m128, m248, m824, mw2, mw1, mw0, h16, fnBase'] until [1803576]
  have ar1 : BitVec.ofNat 64 bp + BitVec.ofNat 64 (i * n * 8) = BitVec.ofNat 64 (bp + 8 * (i * n)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have rd0 : M.readLE (sp + 432 + (8 * i + 2 * (8 * i) - 24)) 8 = bp + 8 * ((i - 1) * n) := by
    rw [show sp + 432 + (8 * i + 2 * (8 * i) - 24) = sp + 432 + 24 * (i - 1) by omega]; exact ep
  have rd1 : M.readLE (8 * i + 2 * (8 * i) - 24 + (sp + 432) + 8) 8 = n := by
    rw [show 8 * i + 2 * (8 * i) - 24 + (sp + 432) + 8 = sp + 440 + 24 * (i - 1) by omega]; exact el
  have rd2 : M.readLE (8 * i + 2 * (8 * i) - 24 + (sp + 432) + 16) 8 = 2 * n := by
    rw [show 8 * i + 2 * (8 * i) - 24 + (sp + 432) + 16 = sp + 448 + 24 * (i - 1) by omega]; exact ec
  janus_run [m1016, m1024, m1032, m224, m128, m248, m824, e1p, e1l, e1c, rd0, rd1, rd2, ar1, fnBase'] until [powHead]
    calls [hP := hA]
  rename_i a0 a1 a2 i1 F1 L1 v1
  have hd1 : ∀ d, d < i → d * n + n ≤ i * n := fun d hd => by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ i by omega); rw [Nat.succ_mul] at this; exact this
  have fA : FP R L sp bp bc M0 (((M.writeLE (sp + 328) 8 (i + 1)).writeLE (sp + 320) 8 (8 * i + 2 * (8 * i))).writeLE
      (sp + 592) 8 (sp + 432 + (8 * i + 2 * (8 * i)))) := by
    repeat (first | exact hF0 | refine FP.write ?_ hLs _ (by omega))
  have fB : FP R L sp bp bc M0 s'.mem := FP.call fA F1 L1 ⟨by omega, by omega⟩
  have u1 := hbw; have u2 := hbm; have u3 := hm.2.2.2
  unfold Apart at u1 u2 u3
  -- a frame word outside the callee's ranges reads through the call
  have thru : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 752 →
      s'.mem.readLE a 8 = (((M.writeLE (sp + 328) 8 (i + 1)).writeLE (sp + 320) 8 (8 * i + 2 * (8 * i))).writeLE
        (sp + 592) 8 (sp + 432 + (8 * i + 2 * (8 * i)))).readLE a 8 := by
    intro a h1 h2
    refine F1.readLE _ _ ?_
    have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
    simp only [outside_append, outside_cons, outside_nil, and_true, hro, true_and]
    omega
  refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?qfp ?qinv ?qrg ?qents ?qent
  all_goals first | (janus_simp; done) | skip
  case qfp => repeat (first | exact fB | refine FP.write ?_ hLs _ (by omega))
  case qinv =>
    have w := hwrt
    repeat (first | exact i1 | refine FvModexp.Expmc.inv_writeLE (Or.inr (w.of_sub (by omega) (by omega))) ?_)
  case qrg => simp only [Memory.regions_writeLE, hP_regions, hrg]
  case qents => exact ents_step hs hi2 hi hE F1 L1
  case qent => exact ent_new hs hi2 hi hE hF0 v1

end FvModexp.Arm64.W2Pro
