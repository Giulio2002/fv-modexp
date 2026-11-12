import FvModexp.Proofs.Arm64.Exp.W2P01
import FvModexp.Proofs.Arm64.Exp.W2PowLoop

/-!
# window-2 prologue (arm64): the whole table `powers[0..4)` (nat.go:1409-1417), `p01 → j4`

Composition of `W2P01.p01run` (entries 0, 1) and `W2PowLoop.powLoop` (entries 2..3); the table values are
`Exp.montPow n m k0 x RR d` (Common/ExpOdd.lean) when `one` holds the value 1.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

/-- the ranges `p01 → j4` may write besides `R.rt` -/
@[reducible] def tw (sp bp n : Nat) : List (Nat × Nat) := qw sp ++ pw sp ++ [(bp, bp + 8 * (5 * n))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem p01pow (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t bp onep rrp rrc xp xc : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp)
    (hba : M.accessible bp (8 * (5 * n)) true = true) (hbb : bp + 8 * (5 * n) ≤ 2 ^ 48)
    (hbh : InRanges bp (8 * (5 * n)) L ∨ Outside bp (8 * (5 * n)) R.rt)
    (hbw : Apart bp (8 * (5 * n)) (sp - 4288) (4288 + 752)) (hbg : Apart (g + 16) 8 bp (8 * (5 * n)))
    (hbm : Apart bp (8 * (5 * n)) mp (8 * n))
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * (5 * n)) onep (8 * n)) (hone1 : M.readLE onep (8 * n) = 1)
    (hrr : Inp R L sp n M rrp) (hbR : Apart bp (8 * (5 * n)) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * (5 * n)) xp (8 * n))
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n) (r528 : M.readLE (sp + 528) 8 = onep)
    (r544 : M.readLE (sp + 544) 8 = rrp) (r256 : M.readLE (sp + 256) 8 = n) (r264 : M.readLE (sp + 264) 8 = rrc)
    (r616 : M.readLE (sp + 616) 8 = xp) (r328 : M.readLE (sp + 328) 8 = xc) (r320 : M.readLE (sp + 320) 8 = n)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 p01) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 (5 * n))
    (h2 : S.regs 2 = BitVec.ofNat 64 (5 * n))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KX : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 j4 → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ tw sp bp n) → LiveFrame M M' L [(bp, bp + 8 * (5 * n))] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE (sp + 224) 8 = (2 ^ 64 - t) % 2 ^ 64 →
      (∀ d, d < 4 → Ent sp n bp (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n))
        (M.readLE rrp (8 * n))) M' d) →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  refine p01run impl hap R hclr hmv ret hret Q b L g sp n mp mc t bp onep rrp rrc xp xc M r18 r29 he hn hn16 hmc hmc'
    ht hm hba hbb hbh hbw hbg hbm hone hbo hrr hbR hx hbx r728 r736 r744 r224 r128 r528 r544 r256 r264 r616 r328
    r320 hok hinv S hpc hsp h0 h1 h2 h18 h28 h29 hmem ?_
  intro S2 M2 a1 a2 a3 a4 a5 a6 a7 hFQ hinv2 hrg2 m224 m248 m824 hE0 hE1
  have hk0 : (2 ^ 64 - t) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have u1 := hbw; have u2 := hbg; have u3 := hbm; have w1 := hm.2.2.2
  unfold Apart at u1 u2 u3 w1
  -- reads through `p01 → powHead`
  have rdq : ∀ a, sp + 120 ≤ a → a + 8 ≤ sp + 752 → a + 8 ≤ sp + 224 ∨ (sp + 232 ≤ a ∧ a + 8 ≤ sp + 248) ∨
      (sp + 256 ≤ a ∧ a + 8 ≤ sp + 312) ∨ (sp + 320 ≤ a ∧ a + 8 ≤ sp + 432) ∨ (sp + 480 ≤ a ∧ a + 8 ≤ sp + 536) ∨
      sp + 544 ≤ a → M2.readLE a 8 = M.readLE a 8 := by
    intro a ha1 ha2 ha3
    refine hFQ.1.readLE _ _ ?_
    have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
    simp only [qw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
    omega
  have hmM2 : M2.readLE mp (8 * n) = M.readLE mp (8 * n) :=
    FvModexp.Expmc.held_readLE hm.2.2.1 hFQ.1 hFQ.2 (by simp only [qw, outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hs : PStatic R L g sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp (5 * n) M2 := by
    have hF' : MemFrame M M2 (R.rt ++ (qw sp ++ [(bp, bp + 8 * (5 * n))])) := by
      rw [← List.append_assoc]; exact hFQ.1
    have hgo : Outside (g + 16) 8 (qw sp ++ [(bp, bp + 8 * (5 * n))]) := by
      unfold Apart at hgw
      simp only [qw, outside_append, outside_cons, outside_nil, and_true]
      omega
    refine ⟨env_frame he hF' hgo, hn, hn16, hmc, hmc', hk0, inp_frame hm hFQ.1, Nat.le_refl _, by omega,
      by rw [hFQ.1.accessible]; exact hba, hbb, hbh, hbw, hbg, hbm, ?_, ?_, ?_, m224, ?_, m248, m824, hok⟩
    · rw [rdq _ (by omega) (by omega) (by omega)]; exact r728
    · rw [rdq _ (by omega) (by omega) (by omega)]; exact r736
    · rw [rdq _ (by omega) (by omega) (by omega)]; exact r744
    · rw [rdq _ (by omega) (by omega) (by omega)]; exact r128
  refine powLoop impl hap R hclr hmv ret hret Q b L g sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp (5 * n) M2 r18 r29
    (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n)) (M.readLE rrp (8 * n))) hs
    ?_ ?_ (4 - 2) 2 S2 M2 rfl (Nat.le_refl _) (by omega) a1 a2 a3 a4 a5 a6 a7
    ⟨MemFrame.refl _ _, LiveFrame.refl _ _ _⟩ hinv2 rfl ?_
  · intro i hi2 hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rw [hmM2]; rfl
  · intro S' M' c1 c2 c3 c4 c5 c6 hFP hinv' hrg' hE
    refine KX S' M' c1 c2 c3 c4 c5 c6 ?_ ?_ hinv' (hrg'.trans hrg2) ?_ hE
    · refine hFQ.1.trans hFP.1 (fun a k ho => ⟨?_, ?_⟩)
      · simp only [tw, outside_append] at ho ⊢; exact ⟨⟨ho.1, ho.2.1.1⟩, ho.2.2⟩
      · simp only [tw, pl, outside_append] at ho ⊢; exact ⟨⟨ho.1, ho.2.1.2⟩, ho.2.2⟩
    · exact hFQ.2.trans hFP.2 (fun _ _ h => h)
    · rw [hFP.1.readLE _ _ ?_]
      · exact m224
      · have hro : Outside (sp + 224) 8 R.rt := hwrt.of_sub (by omega) (by omega)
        simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
        omega
  · intro d hd
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · refine ⟨?_, hE0.2⟩
      rw [hE0.1, hone1]; rfl
    · exact hE1

end FvModexp.Arm64.W2Pro
