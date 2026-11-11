import FvModexp.Proofs.Arm64.Nat.NatAddNorm
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.add` (arm64): the body for `len y ≤ len x`, as a `Summary` at the entry (WIP)

Used at the self-call `z.add(y, x)` (which returns inside `nat.add`, so an `Ensures` cannot serve it) and, by
`Summary.returns`, for the `len y ≤ len x` case of `ens`. Stack: frame 160 + `addVW` 4144 = 4304.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatAdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem body (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hVW : ∀ b L zp zl zc xp xl xc y, AddVWEns impl R b L zp zl zc xp xl xc y)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = yp ∧ s.regs 7 = yl ∧
        s.regs 8 = yc ∧ yl.toNat ≤ xl.toNat ∧ PreS 4304 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hyx, hpre⟩
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hty, hxc, hyc, hxc40, hyc40, hx40, hy40, hz40, hzl, hzw,
    hxacc, hx48, hxh, hxnorm, hynorm, hxw, hyacc, hy48, hyh, hyw, hinv, hok, hmvok⟩ := hpre'
  have hc1 : CodeIn ((Extracted.program.onlySegments [addVVfn]).link impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hc2 : CodeIn ((Extracted.program.onlySegments [addVWfn]).link impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibNatAdd.names
  have hVV' : ∀ b L, Summary (LibNatAdd.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (fun s s' => GoABI0.Ret0 s s' (VVLQ R b L s)) := fun b L => AddVVHyp.live (Janus.Contracts.EqHashModel.Summary.of_codeIn hc1 (addVVHyp impl hap)) R b L
  have hVW' := fun b L => Ensures.toSummaryRegs7 (hVW b L) (noExit_restrict hap [addVWfn]) hc2
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  clear hc1 hc2 hc3 hVW hmk hmv
  have hwt : Apart wordT 16 (s.sp.toNat - 4304) (4304 + 80) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok hwt
  simp only [LiveSep, win] at hLs
  by_cases hx0 : xl.toNat = 0
  · sorry
  by_cases hy0 : yl.toNat = 0
  · sorry
  by_cases hz : zc.toNat < xl.toNat + 1
  · sorry
  · have hzc0 : 0 < zc.toNat := by omega
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hzc0
    obtain ⟨hzw', hzg, hzx, hzy⟩ := hzw hzc0
    simp only [Outside, and_true] at hzw'
    have ha1 : s.mem.accessible zp.toNat (8 * yl.toNat) true = true :=
      Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
    have hzx1 : zp.toNat = xp.toNat ∨ Apart zp.toNat (8 * yl.toNat) xp.toNat (8 * yl.toNat) := by
      rcases hzx with h | h
      · exact Or.inl (by rw [h])
      · right; unfold Apart at h ⊢; omega
    have hzy1 : zp.toNat = yp.toNat ∨ Apart zp.toNat (8 * yl.toNat) yp.toNat (8 * yl.toNat) := by
      rcases hzy with h | h
      · exact Or.inl (by rw [h])
      · right; unfold Apart at h ⊢; omega
    have hzr : zp.toNat + 8 * yl.toNat ≤ s.sp.toNat - 160 + 80 ∨ s.sp.toNat - 160 + 80 + 8 ≤ zp.toNat := by omega
    have hzh1 : InRanges zp.toNat (8 * yl.toNat) L ∨ Outside zp.toNat (8 * yl.toNat) R.rt :=
      hzh.sub (Nat.le_refl _) (by omega)
    have hzg1 : zp.toNat + 8 * yl.toNat ≤ (s.regs 28).toNat + 16 ∨ (s.regs 28).toNat + 16 + 8 ≤ zp.toNat := by
      unfold Apart at hzg; omega
    by_cases hxy : yl.toNat = xl.toNat
    · sorry
    have hlt : yl.toNat < xl.toNat := by omega
    have hm1 : ((yl - zc).sshiftRight 63).toNat = 18446744073709551615 := sshr63_of_lt _ _ (by omega) (by omega)
    have hm2 : ((yl - xc).sshiftRight 63).toNat = 18446744073709551615 := sshr63_of_lt _ _ (by omega) (by omega)
    have hand : yl.toNat &&& 18446744073709551615 = yl.toNat := and_ones64 _ yl.isLt
    have hs1 : (18446744073709551616 - yl.toNat + xl.toNat) % 18446744073709551616 = xl.toNat - yl.toNat :=
      sub_mod64 _ _ (by omega) xl.isLt
    have hs2 : (18446744073709551616 - yl.toNat + xc.toNat) % 18446744073709551616 = xc.toNat - yl.toNat :=
      sub_mod64 _ _ (by omega) xc.isLt
    have hs3 : (18446744073709551616 - yl.toNat + zc.toNat) % 18446744073709551616 = zc.toNat - yl.toNat :=
      sub_mod64 _ _ (by omega) zc.isLt
    have hmz : (zp.toNat + 8 * yl.toNat) % 18446744073709551616 = zp.toNat + 8 * yl.toNat := mod64_of_lt _ (by omega)
    have hmx : (xp.toNat + 8 * yl.toNat) % 18446744073709551616 = xp.toNat + 8 * yl.toNat := mod64_of_lt _ (by omega)
    have hzh2 : InRanges (zp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) L ∨
        Outside (zp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) R.rt := hzh.sub (by omega) (by omega)
    have hzb1 : s.mem.accessible (zp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) true = true :=
      Memory.accessible_mono _ hzacc (by omega) (by omega)
    have hzb2 := Memory.accessible_weaken _ hzb1
    have hxb : s.mem.accessible (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) false = true :=
      Memory.accessible_mono _ hxacc (by omega) (by omega)
    have hxh2 : InRanges (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) L ∨
        Outside (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) R.rt := hxh.sub (by omega) (by omega)
    have hLsW : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 160 - 4144 ∨ s.sp.toNat - 160 + 32 ≤ r.fst := by
      intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; omega
    have hxw' := hxw; simp only [win, Outside, and_true] at hxw'
    janus_run [hm1, hm2, hand, hs1, hs2, hs3, hmz, hmx] until [segAddr Extracted.program addVWfn] calls [hmk'.pos, hmv', hVV']
    all_goals trace_state
    all_goals sorry

end FvModexp.Arm64.NatAdd
