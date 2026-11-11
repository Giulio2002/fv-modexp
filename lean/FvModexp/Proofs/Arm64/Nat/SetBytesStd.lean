import FvModexp.Proofs.Arm64.Nat.SetBytesStdWord
import FvModexp.Proofs.Arm64.Nat.SetBytesStdMid

/-!
# PILOT: `nat.setBytes` (standard library copy), arm64 — the theorem `ens` and the callee summary `sum`

See `docs/CONVENTIONS.md`. Modules: `SetBytesDefs` (statement pieces), `SetBytesNorm`, `SetBytesByte`, `SetBytesWord`
(one loop each), `SetBytesMid` (the loop-head facts after `nat.make`), this module (prologue, `nat.make` with its
`makeslice` call, the four paths: empty buffer, reuse, `make(nat, 1)`, `make(nat, n, n+4)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SetBytesStd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn) [zp, zl, zc, bp, bl, bc]
      (Pre R b L zp zc bp bl) (Post R b L zp zc bp bl) := by
  intro ret hret s hs ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hlive, hbl, hbp, hbacc,
    hheld, hbwin, hzb, hzw, hinv, hok⟩
  have hmk' := MakesliceLiveContract.of_codeIn (codeIn_ofImpl_restrict_of_apart hap [fn]) hmk
  have hLs0 := hLs
  janus_intro hs
  have hwt : Apart wordT 16 (s.sp.toNat - 4160) (4160 + 48) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok hwt
  simp only [LiveSep, win] at hLs
  have hbw := hbwin
  simp only [Outside, and_true] at hbw
  have hzc : zc.toNat < 2 ^ 63 := by
    by_cases hz0 : zc.toNat = 0
    · omega
    · have := (hlive (by omega)).2.2.2; omega
  by_cases h0 : bl.toNat = 0
  · -- the empty buffer: `z[:0]`, no loop
    clear hok
    have hz' : ¬ ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by omega
    janus_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, toInt_ushiftRight]
    refine post_empty ?_ (by janus_simp) (by janus_simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega) (by janus_simp) h0 hlive hLs0 hout hb' hinv
    simp only [winA]; janus_frame
  · by_cases hz : zc.toNat < nW bl
    · obtain ⟨hok1, hcost⟩ := hok hz
      have hbs := blockSize_le_allocCost (8 * makeCap (nW bl)) true
      clear hok
      by_cases h1 : nW bl = 1
      · rw [h1, show makeCap 1 = 1 from rfl] at hok1 hbs
        have hb8 : blockSize (8 * 1) true ≤ b := by unfold makeCost at hcost; rw [h1] at hcost; exact Nat.le_trans hbs hcost
        simp only [nW] at h1 hz
        have hz' : ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by omega
        janus_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow, toInt_ushiftRight] until [hWord] calls [hmk'.pos]
        rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ _
        refine wordLoop impl R b L zp zc bp bl ret hret s ptr.toNat 1 _ _ hbl (by omega) ⟨hb', ha, hal⟩ hw hbacc hbp
          (bl.toNat / 8) _ m ptr 1#64 1#64 bl 0#64 (by omega) (by simp) rfl (by simp [nW]; omega) (by simp)
          (mid_of_alloc hLs0 hout hb' hheld hbwin (by janus_simp) (by janus_simp) ?_ ?_ hLF hMF hAp hIn (by omega) hacc h8
            hinv' (by omega) (by simp only [makeCost, makeCap, allocCost, nW]; rw [h1]; decide) (by simp only [nW]; omega))
          (by simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
          (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) rfl
        · intro a k h1 h2
          janus_simp
        · simp only [winA]; janus_frame
      · rw [show makeCap (nW bl) = nW bl + 4 by unfold makeCap; simp [h1]] at hok1 hbs
        have hbn : blockSize (8 * ((bl.toNat + 7) / 8 + 4)) true ≤ b := by
          unfold makeCost makeCap at hcost; rw [if_neg h1] at hcost; exact Nat.le_trans hbs hcost
        simp only [nW] at h1 hz hok1 hbs
        have hz' : ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by omega
        janus_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow, toInt_ushiftRight] until [hWord] calls [hmk'.pos]
        rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ _
        have hsz := (by janus_assumption : 8 * ((bl.toNat + 7) / 8 + 4) ≤ blockSize (8 * ((bl.toNat + 7) / 8 + 4)) true)
        refine wordLoop impl R b L zp zc bp bl ret hret s ptr.toNat ((bl.toNat + 7) / 8 + 4) _ _ hbl (by omega)
          ⟨hb', ha, hal⟩ hw hbacc hbp (bl.toNat / 8) _ m ptr (BitVec.ofNat 64 ((bl.toNat + 7) / 8))
          (BitVec.ofNat 64 ((bl.toNat + 7) / 8 + 4)) bl 0#64 (by omega) (by simp) rfl
          (by simp only [BitVec.toNat_ofNat, nW]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
          (mid_of_alloc hLs0 hout hb' hheld hbwin (by janus_simp) (by janus_simp) ?_ ?_ hLF hMF hAp hIn (by omega) hacc
            (h8 (Or.inr (by omega))) hinv' (by omega)
            (by unfold makeCost makeCap nW; rw [if_neg h1]; exact Nat.le_trans (blockSize_le_allocCost _ true) (Nat.le_refl _))
            (by simp only [nW]; omega))
          (by simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
          (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) rfl
        · intro a k h1 h2
          janus_simp
        · simp only [winA]; janus_frame

    · -- reuse `z`
      clear hok
      have hz' : ¬ ((zc.toNat : Int) < (((bl.toNat + 7) / 8 : Nat) : Int)) := by simp only [nW] at hz; omega
      janus_run [asr_small_bv, asr63_small, sshiftRight_small, toInt_small, asr_small_toNat, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, toInt_ushiftRight] until [hWord]
      have hz0 : 0 < zc.toNat := by simp only [nW] at hz; omega
      refine wordLoop impl R b L zp zc bp bl ret hret s zp.toNat zc.toNat L b hbl (by omega) ⟨hb', ha, hal⟩ hw hbacc hbp
        (bl.toNat / 8) _ _ zp ((bl + 7#64) >>> 3) zc bl 0#64 (by omega) (by simp) rfl
        (by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; janus_simp) rfl
        (mid_of_reuse hlive hzb hzw hLs0 hout hb' hinv (by omega) hz0 (by janus_simp) (by janus_simp) ?_ ?_)
        (by simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
        (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) rfl
      · intro a k h1 h2
        janus_simp
      · simp only [winA]; janus_frame

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ [fn]`
(`docs/CONVENTIONS.md` §4): `janus_run … calls [SetBytes.sum impl hap R hmk b L zp zl zc bp bl bc ms (by decide)]`. -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc bp bl bc : BitVec 64) (ms : List String)
    (hsub : ∀ x, [fn].contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk b L zp zl zc bp bl bc) (noExit_restrict hap [fn])
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.SetBytesStd

