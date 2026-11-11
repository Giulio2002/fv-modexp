import FvModexp.Proofs.Arm64.Top.RunRel
import FvModexp.Proofs.Arm64.Top.RunLMath
import FvModexp.Proofs.Common.GenReg

/-! # `Run` (arm64): `B3` to `C0` — the length checks (`Uint64`, `BitLen`, EIP-7823, the zero case, the error return) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem hLx (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hrecv : s.mem.readLE c.toNat 3 = 65793) (hokn : R.ok (cA "runtime.newobject") [errT])
    (hcostE : 3 * makeCost 4 + allocCost 16 ≤ b)
    (Q : Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcB3)
    (hr0 : (S.regs 0).toNat = S.mem.readLE (s.sp.toNat - 96) 8) (hr1 : (S.regs 1).toNat = S.mem.readLE (s.sp.toNat - 88) 8) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hsl, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF,
    hhd⟩ := hrel
  have hno' : NewobjectLiveContract (LibRun.program.link impl) (cA "runtime.newobject") 4096 R :=
    NewobjectLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hno
  have hap1 := hap.1
  have hS : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := hMF.accessible
  have hA : ∀ k, k < 3 → S.mem.readLE (hdrAt s k + 8) 8 ≠ 0 →
      S.mem.accessible (S.mem.readLE (hdrAt s k) 8) (8 * S.mem.readLE (hdrAt s k + 8) 8) false = true ∧
      S.mem.readLE (hdrAt s k) 8 + 8 * S.mem.readLE (hdrAt s k + 8) 8 ≤ 2 ^ 48 := by
    intro k hk hn
    obtain ⟨⟨-, -, -, hcl⟩, -, hac⟩ := hhd k hk
    obtain ⟨-, h2, h3⟩ := hac (by omega)
    refine ⟨Memory.accessible_read_of_write _ ?_, by omega⟩
    rw [hS]; exact Memory.accessible_mono _ h2 (Nat.le_refl _) (by omega)
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  have e0 : hdrAt s 0 = s.sp.toNat - 32 := by simp only [hdrAt]; omega
  have e1 : hdrAt s 1 = s.sp.toNat - 64 := by simp only [hdrAt]; omega
  have e2 : hdrAt s 2 = s.sp.toNat - 96 := by simp only [hdrAt]; omega
  have f0 : s.sp.toNat - 32 + 8 = s.sp.toNat - 24 := by omega
  have f1 : s.sp.toNat - 64 + 8 = s.sp.toNat - 56 := by omega
  have f2 : s.sp.toNat - 96 + 8 = s.sp.toNat - 88 := by omega
  have hle : ∀ k, k < 3 → S.mem.readLE (hdrAt s k + 8) 8 ≤ 4 := fun k hk => (hhd k hk).1.2.2.1
  have hl0 := hle 0 (by omega); rw [e0, f0] at hl0
  have hl1 := hle 1 (by omega); rw [e1, f1] at hl1
  have hl2 := hle 2 (by omega); rw [e2, f2] at hl2
  clear hle
  have hnt : ∀ k, k < 3 → S.mem.readLE (hdrAt s k + 8) 8 = 0 ∨
      S.mem.readLE (S.mem.readLE (hdrAt s k) 8 + 8 * (S.mem.readLE (hdrAt s k + 8) 8 - 1)) 8 ≠ 0 :=
    fun k hk => (hhd k hk).1.2.1
  have ht0 := hnt 0 (by omega); rw [e0, f0] at ht0
  have ht1 := hnt 1 (by omega); rw [e1, f1] at ht1
  have ht2 := hnt 2 (by omega); rw [e2, f2] at ht2
  clear hnt
  by_cases hz0 : S.mem.readLE (s.sp.toNat - 24) 8 = 0
  · sorry
  by_cases hz1 : S.mem.readLE (s.sp.toNat - 56) 8 = 0
  · sorry
  by_cases hz2 : S.mem.readLE (s.sp.toNat - 88) 8 = 0
  · sorry
  · have ⟨ha0, hb0⟩ := hA 0 (by omega) (by rw [e0, f0]; exact hz0)
    have ⟨ha1, hb1⟩ := hA 1 (by omega) (by rw [e1, f1]; exact hz1)
    have ⟨ha2, hb2⟩ := hA 2 (by omega) (by rw [e2, f2]; exact hz2)
    rw [e0, f0] at ha0 hb0
    rw [e1, f1] at ha1 hb1
    rw [e2, f2] at ha2 hb2
    clear hA
    have hr1' : S.regs 1 = BitVec.ofNat 64 (S.mem.readLE (s.sp.toNat - 88) 8) := by
      apply BitVec.eq_of_toNat_eq; rw [hr1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hr0' : S.regs 0 = BitVec.ofNat 64 (S.mem.readLE (s.sp.toNat - 96) 8) := by
      apply BitVec.eq_of_toNat_eq; rw [hr0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hLSn : ∀ r ∈ L1, (r.1 + (r.2 - r.1) ≤ BitVec.toNat s.sp - 624 - 4096 ∨ BitVec.toNat s.sp - 624 - 8 ≤ r.1) ∧
        (r.1 + (r.2 - r.1) ≤ BitVec.toNat s.sp - 624 + 8 ∨ BitVec.toNat s.sp - 624 + 8 + 8 ≤ r.1) := by
      intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
    have hT1 : S.mem.accessible 2762976 16 false = true := by
      janus_data hdS; exact Memory.accessible_mono _ h_data3 (Nat.le_refl _) (by omega)
    have hT2 : S.mem.readLE 2762976 8 = 16 := by
      janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
    have hT3 : blockSize 16 (S.mem.readLE 2762984 8 == 0) ≤ b1 := by
      have := blockSize_le_allocCost 16 (S.mem.readLE 2762984 8 == 0); simp only [allocCost] at this
      simp only [makeCost, allocCost, makeCap] at hbud hcostE; omega
    have hq0 := msb_sub_one_small _ (Nat.pos_of_ne_zero hz0) hl0
    have hq1 := msb_sub_one_small _ (Nat.pos_of_ne_zero hz1) hl1
    have hq2 := msb_sub_one_small _ (Nat.pos_of_ne_zero hz2) hl2
    have hc1 : S.mem.readLE (c.toNat + 1) 1 = 1 := by
      rw [← hcS] at hrecv
      have h3 := Memory.readLE_add S.mem c.toNat 1 2
      have h4 := Memory.readLE_add S.mem (c.toNat + 1) 1 1
      have l1 := Memory.readLE_lt S.mem c.toNat 1
      have l2 := Memory.readLE_lt S.mem (c.toNat + 1) 1
      have l3 := Memory.readLE_lt S.mem (c.toNat + 1 + 1) 1
      rw [hrecv] at h3; rw [h4] at h3; omega
    clear hinS hcS hext hbud hLF hhd hsl hLs hcheld hheld hpw hcw hlcp hcp48 hpacc hp hd hno
      e0 e1 e2 f0 f1 f2 hdS hro
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hr0', hr1', hq0, hq1, hq2] until [segAddr Extracted.program fn + 0x2a8]
    generalize hx0 : BitVec.ofNat 64 (S.mem.readLE (S.mem.readLE (BitVec.toNat s.sp - 32) 8 +
      8 * (S.mem.readLE (BitVec.toNat s.sp - 24) 8 - 1)) 8) = x0
    janus_run [hq1, hq2] until [segAddr Extracted.program fn + 0x2e8]
    generalize hx1 : BitVec.ofNat 64 (S.mem.readLE (S.mem.readLE (BitVec.toNat s.sp - 64) 8 +
      8 * (S.mem.readLE (BitVec.toNat s.sp - 56) 8 - 1)) 8) = x1
    janus_run [hq2] until [segAddr Extracted.program fn + 0x320]
    generalize hx2 : BitVec.ofNat 64 (S.mem.readLE (S.mem.readLE (BitVec.toNat s.sp - 96) 8 +
      8 * (S.mem.readLE (BitVec.toNat s.sp - 88) 8 - 1)) 8) = x2
    janus_run [hc1] until [segAddr Extracted.program fn + 0x34c]
    gen_reg 6 as bl0 with hB0
    gen_reg 7 as bl1 with hB1
    gen_reg 9 as bl2 with hB2
    have k0 : 64 * (S.mem.readLE (s.sp.toNat - 24) 8 - 1) < bl0.toNat ∧ bl0.toNat ≤ 64 * S.mem.readLE (s.sp.toNat - 24) 8 := by
      rw [← hB0]; refine blr_val _ _ ?_ ?_ (Nat.pos_of_ne_zero hz0) hl0
      · repeat apply or_pos_left'
        rw [← hx0]; exact toNat_ofNat_readLE_pos _ _ (ht0.resolve_left hz0)
      · repeat (first | apply Nat.or_lt_two_pow | exact BitVec.isLt _)
    have k1 : 64 * (S.mem.readLE (s.sp.toNat - 56) 8 - 1) < bl1.toNat ∧ bl1.toNat ≤ 64 * S.mem.readLE (s.sp.toNat - 56) 8 := by
      rw [← hB1]; refine blr_val _ _ ?_ ?_ (Nat.pos_of_ne_zero hz1) hl1
      · repeat apply or_pos_left'
        rw [← hx1]; exact toNat_ofNat_readLE_pos _ _ (ht1.resolve_left hz1)
      · repeat (first | apply Nat.or_lt_two_pow | exact BitVec.isLt _)
    have k2 : 64 * (S.mem.readLE (s.sp.toNat - 88) 8 - 1) < bl2.toNat ∧ bl2.toNat ≤ 64 * S.mem.readLE (s.sp.toNat - 88) 8 := by
      rw [← hB2]; refine blr_val _ _ ?_ ?_ (Nat.pos_of_ne_zero hz2) hl2
      · repeat apply or_pos_left'
        rw [← hx2]; exact toNat_ofNat_readLE_pos _ _ (ht2.resolve_left hz2)
      · repeat (first | apply Nat.or_lt_two_pow | exact BitVec.isLt _)
    clear hB0 hB1 hB2
    have hnoP := hno'.pos L1 b1
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hc1, hT2] until [segAddr Extracted.program fn + 0x424] calls [hnoP]
    all_goals trace_state
    all_goals sorry

end FvModexp.Arm64.Run
