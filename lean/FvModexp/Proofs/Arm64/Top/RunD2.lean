import FvModexp.Proofs.Arm64.Top.RunD1

/-! # `Run` (arm64): `D1` to `D2` — the exponent operand (`getData(input, baseLen, expLen)`, patched `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem d2x (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 1 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcD1) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, hk1,
    hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF, hop⟩ := hrel
  obtain ⟨hk1a, hk1b⟩ := hk1 (Nat.le_refl _)
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
  by_cases hdir : min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1 ≤ len.toNat - 96
  · have hc : (len.toNat - 96 < min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1) = False := by simp; omega
    have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 1)) (by simp; omega)
    janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hk1a, hk1b, hc, hIe, toInt_ite, toNat_ite,
      toInt_small] until [segAddr Extracted.program fn + 0x64c]
    all_goals trace_state
    all_goals sorry
  · sorry

end FvModexp.Arm64.Run
