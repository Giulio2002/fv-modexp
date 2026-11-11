import FvModexp.Proofs.Amd64.Nat.SetBytesStdWord
import FvModexp.Proofs.Amd64.Nat.SetBytesStdMid

/-!
# PILOT: `nat.setBytes` (standard library copy), amd64 — the theorem `ens` and the callee summary `sum`

As the arm64 module (`FvModexp.Arm64.SetBytes`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.SetBytesStd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn) [zp, zl, zc, bp, bl, bc]
      (Pre R b L zp zc bp bl) (Post R b L zp zc bp bl) := by
  intro ret hret s hs ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro⟩, hty, hlive, hbl, hbp, hbacc,
    hheld, hbwin, hzb, hzw, hinv, hok⟩
  have hmk' := MakesliceLiveContract64.of_codeIn (codeIn_ofImpl_restrict_of_apart64 hap [fn]) hmk
  have hLs0 := hLs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  janus64_intro hs
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 4160) (4160 + 48) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus64_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok hwt
  simp only [LiveSep, win] at hLs
  have hbw := hbwin
  simp only [Outside, and_true] at hbw
  have hzc : zc.toNat < 2 ^ 63 := by
    by_cases hz0 : zc.toNat = 0
    · omega
    · have := (hlive (by omega)).2.2.2; omega
  have hb7 : (bl + 7#64).toNat < 2 ^ 63 := by rw [BitVec.toNat_add]; simp; omega
  have hsa : (bl + 7#64).sshiftRight 63 = 0#64 := by
    rw [sshiftRight_small _ hb7]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
  have hsb : (bl + 7#64).sshiftRight 3 = (bl + 7#64) >>> 3 := sshiftRight_small _ hb7 3
  have hsc : (bl + 7#64) >>> 124 = 0#64 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
  by_cases h0 : bl.toNat = 0
  · clear hok
    have hz' : ¬ ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by omega
    janus64_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, toInt_ushiftRight, BitVec.msb_eq_decide, hsa, hsb, hsc, BitVec.add_zero]
    refine post_empty (by janus64_simp) ?_ (by janus64_simp) (by janus64_simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
      (by janus64_simp) h0 hlive hLs0 hout hinv
    simp only [win]; janus_frame
  · by_cases hz : zc.toNat < nW bl
    · obtain ⟨hok1, hcost⟩ := hok hz
      have hbs := blockSize_le_allocCost (8 * makeCap (nW bl)) true
      clear hok
      by_cases h1 : nW bl = 1
      · rw [h1, show makeCap 1 = 1 from rfl] at hok1 hbs
        have hb8 : blockSize (8 * 1) true ≤ b := by unfold makeCost at hcost; rw [h1] at hcost; exact Nat.le_trans hbs hcost
        simp only [nW] at h1 hz
        have hz' : ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by omega
        janus64_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, toInt_ushiftRight, BitVec.msb_eq_decide, hsa, hsb, hsc, BitVec.add_zero] until [hWord] calls [hmk'.pos]
        rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ _
        refine wordLoop impl R b L zp zc bp bl ret hret s ptr.toNat 1 _ _ hbl (by omega) ⟨hb', ha, hal⟩ hw hbacc hbp
          (bl.toNat / 8) _ m ptr 1#64 1#64 bl 0#64 (by omega) (by simp) rfl (by simp [nW]; omega) (by simp)
          (mid_of_alloc hLs0 hout hb' hheld hbwin ?_ ?_ ?_ ?_ hLF hMF hAp hIn (by omega) hacc h8
            hinv' (by omega) (by simp only [makeCost, makeCap, allocCost, nW]; rw [h1]; decide) (by simp only [nW]; omega))
          (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
        · janus64_simp
        · janus64_simp
        · intro a k h1 h2
          janus64_simp
        · simp only [win]; janus_frame
        all_goals janus64_simp
      · rw [show makeCap (nW bl) = nW bl + 4 by unfold makeCap; simp [h1]] at hok1 hbs
        have hbn : blockSize (8 * ((bl.toNat + 7) / 8 + 4)) true ≤ b := by
          unfold makeCost makeCap at hcost; rw [if_neg h1] at hcost; exact Nat.le_trans hbs hcost
        simp only [nW] at h1 hz hok1 hbs
        have hz' : ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by omega
        janus64_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, toInt_ushiftRight, BitVec.msb_eq_decide, hsa, hsb, hsc, BitVec.add_zero] until [hWord] calls [hmk'.pos]
        rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ _
        have hsz := (by janus_assumption : 8 * ((bl.toNat + 7) / 8 + 4) ≤ blockSize (8 * ((bl.toNat + 7) / 8 + 4)) true)
        refine wordLoop impl R b L zp zc bp bl ret hret s ptr.toNat ((bl.toNat + 7) / 8 + 4) _ _ hbl (by omega)
          ⟨hb', ha, hal⟩ hw hbacc hbp (bl.toNat / 8) _ m ptr (BitVec.ofNat 64 ((bl.toNat + 7) / 8))
          (BitVec.ofNat 64 ((bl.toNat + 7) / 8 + 4)) bl 0#64 (by omega) (by simp) rfl
          (by simp only [BitVec.toNat_ofNat, nW]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
          (mid_of_alloc hLs0 hout hb' hheld hbwin ?_ ?_ ?_ ?_ hLF hMF hAp hIn (by omega) hacc
            (h8 (Or.inr (by omega))) hinv' (by omega)
            (by unfold makeCost makeCap nW; rw [if_neg h1]; exact Nat.le_trans (blockSize_le_allocCost _ true) (Nat.le_refl _))
            (by simp only [nW]; omega))
          (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
        · janus64_simp
        · janus64_simp
        · intro a k h1 h2
          janus64_simp
        · simp only [win]; janus_frame
        all_goals janus64_simp
    · clear hok
      have hz' : ¬ ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by simp only [nW] at hz; omega
      janus64_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, toInt_ushiftRight, BitVec.msb_eq_decide, hsa, hsb, hsc, BitVec.add_zero] until [hWord]
      have hz0 : 0 < zc.toNat := by simp only [nW] at hz; omega
      refine wordLoop impl R b L zp zc bp bl ret hret s zp.toNat zc.toNat L b hbl (by omega) ⟨hb', ha, hal⟩ hw hbacc hbp
        (bl.toNat / 8) _ _ zp ((bl + 7#64) >>> 3) zc bl 0#64 (by omega) (by simp) rfl
        (by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; janus64_simp) rfl
        (mid_of_reuse hlive hzb hzw hLs0 hout hb' hinv (by omega) hz0 ?_ ?_ ?_ ?_)
        (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
      · janus64_simp
      · janus64_simp
      · intro a k h1 h2
        janus64_simp
      · simp only [win]; janus_frame
      all_goals janus64_simp

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ [fn]` (amd64). -/
def sum (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) (ms : List String)
    (hsub : ∀ x, [fn].contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk b L zp zl zc bp bl bc) (FvModexp.A64.noExit_restrict64 hap [fn])
    (by simp [numIntRegs]) (FvModexp.A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.SetBytesStd
