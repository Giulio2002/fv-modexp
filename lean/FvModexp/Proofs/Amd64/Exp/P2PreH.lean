import FvModexp.Proofs.Amd64.Exp.P2PreSq

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the loop head (`+0x388`) → `powers[i].sqr(stk, powers[i/2])` →
`JA` (agent divmc s65; twin of infra's `Arm64/Exp/P2PreH`)

`segH`: `HeadJ i` for `i + 2 ≤ len` from `JA i`: the loop test `i < len` (`+0x390`), `i/2` (`+0x399…+0x3a4`), the bounds
checks of `powers[i/2]`, `powers[i]`, `powers[i+1]` (`+0x3af/+0x3c0/+0x3ce`), the locals `i`, `3 i` (`+0x3d7/+0x3e5`,
`rs_head`), the argument loads and the call `sqr` (`+0x40e`, `callSqrH`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segH (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc) (hkc : 4608 ≤ kc) {i : Nat}
    (kA : JA impl R kc b L st pw pl ws lm x xl s i) (hip : i + 2 ≤ pl) :
    HeadJ impl R kc b L st pw pl ws lm x xl s i := by
  intro S bp L1 b1 hpre hpc hfr h0 h2 hc hd ht hi2 hi _ hb
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hfr' := hfr
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr'
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hR64 := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hwm : S.mem.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hpwm : S.mem.accessible pw (24 * pl) true = true := by
    rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, e2, -, -, -, -, -, e8, e9, -⟩ := hc.sl
  have f144 : S.mem.readLE ((s.regs 4).toNat - 176 + 144) 8 = pl := by
    rw [show (s.regs 4).toNat - 176 + 144 = (s.regs 4).toNat - 32 by omega]; exact e8
  have f136 : S.mem.readLE ((s.regs 4).toNat - 176 + 136) 8 = pl := by
    rw [show (s.regs 4).toNat - 176 + 136 = (s.regs 4).toNat - 40 by omega]; exact e9
  have f184 : S.mem.readLE ((s.regs 4).toNat - 176 + 184) 8 = st := by
    rw [show (s.regs 4).toNat - 176 + 184 = (s.regs 4).toNat + 8 by omega]; exact e2
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hpw48 := hf.pw48
  have hi63 : i < 2 ^ 63 := by omega
  have hs63 : BitVec.ofNat 64 i >>> 63 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
  have hasr : BitVec.sshiftRight (BitVec.ofNat 64 i >>> 63 + BitVec.ofNat 64 i) 1 = BitVec.ofNat 64 (i / 2) := by
    rw [hs63, BitVec.zero_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.2 (by rw [BitVec.toNat_ofNat]; omega)),
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hq1 : i / 2 < pl := by omega
  have hq2 : i < pl := by omega
  have hq3 : i + 1 < pl := by omega
  have hpw := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpw
  obtain ⟨t0, t1, t2⟩ := ht i (Nat.le_refl _) (by omega)
  obtain ⟨d0, d2, -, -, -⟩ := hd (i / 2) (by omega)
  have m0 : S.mem.readLE (pw + (i + i * 2) * 8) 8 = bp + 8 * (i * W lm) := by
    rw [show pw + (i + i * 2) * 8 = pw + 24 * i by omega]; exact t0
  have m1 : S.mem.readLE (pw + (i + i * 2) * 8 + 8) 8 = W lm := by
    rw [show pw + (i + i * 2) * 8 + 8 = pw + 24 * i + 8 by omega]; exact t1
  have m2 : S.mem.readLE (pw + (i + i * 2) * 8 + 16) 8 = 2 * W lm := by
    rw [show pw + (i + i * 2) * 8 + 16 = pw + 24 * i + 16 by omega]; exact t2
  have m4 : S.mem.readLE (pw + (i / 2 + i / 2 * 2) * 8) 8 = bp + 8 * (i / 2 * W lm) := by
    rw [show pw + (i / 2 + i / 2 * 2) * 8 = pw + 24 * (i / 2) by omega]; exact d0
  have m5 : S.mem.readLE (pw + (i / 2 + i / 2 * 2) * 8 + 8) 8 = S.mem.readLE (pw + 24 * (i / 2) + 8) 8 := by
    rw [show pw + (i / 2 + i / 2 * 2) * 8 + 8 = pw + 24 * (i / 2) + 8 by omega]
  have m6 : S.mem.readLE (pw + (i / 2 + i / 2 * 2) * 8 + 16) 8 = W lm := by
    rw [show pw + (i / 2 + i / 2 * 2) * 8 + 16 = pw + 24 * (i / 2) + 16 by omega]; exact d2
  have hxl : (memH s S.mem i).readLE (pw + 24 * (i / 2) + 8) 8 = S.mem.readLE (pw + 24 * (i / 2) + 8) 8 := by
    simp only [memH]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrs := rs_head hpre hkc hc hd ht hip
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hpre hc hd ht t0 t1 t2 d0 d2
  unfold Goal
  janus64_run [f144, f136, f184, hwm, hpwm, hi63, hasr, m0, m1, m2, m4, m5, m6] until [6229984]
  refine callSqrH hap hns hnf hsq hkS1 hkS hkc hpreB.h kA hrs hi2 hi hip hb _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl
    ?_ ?_ ?_ ?_ ?_ hxl ?_ ?_
  all_goals first | exact hfs | exact hdf | exact hsub8 | (janus64_simp <;> first | exact hx15 | rfl)

end

end FvModexp.Amd64.P2Pre
