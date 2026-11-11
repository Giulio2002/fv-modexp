import FvModexp.Proofs.Amd64.Nat.LibAddTo
import FvModexp.Proofs.Amd64.Nat.AsmCallees
import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.DivmcBits

/-!
# `addTo(z, x nat)` (go-bigmodexpfix nat.go:234), amd64

See the arm64 twin `FvModexp.Arm64.AddTo`. Frame `0x50` + saved `RBP` (`0x58`), spills `RAX, RBX, RCX, RDI, RSI` at
`RSP + 8 … RSP + 48` (`above = 48`); `addVW` (`stk 4136`) is called with `RSP' = RSP - 0x60`: `stk = 0x60 + 4136 = 4232`.
`addVV.abi0` takes its frame at `RSP' + 8 …` (`RSP' = RSP - 0x60`, the callee's `RSP`), result word at `RSP - 16`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.AddTo

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addTo"
def names : List String := LibAddTo.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hVW : ∀ b L zp zl zc xp xl xc y, AddVWEns impl R b L zp zl zc xp xl xc y)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc]
      (fun s => CallEnvND R L s 4232 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
        NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4232 48) ∧ zc.toNat < 2 ^ 63 ∧
        s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
        Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4232 48) ∧
        (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
        Apart zp.toNat (8 * zl.toNat) ((s.regs 14).toNat + 16) 8 ∧ Apart zp.toNat (8 * zl.toNat) (s.fsBase.toNat - 8) 8 ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem))
      (fun s s' => natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ win s 4232 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)]) := by
  rw [show names = LibAddTo.names from rfl, ← LibAddTo.eq_only]
  have hVV := addVVHyp impl hap
  intro ret hret s hs ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, ⟨htb, htr, htg⟩, htrt, htw⟩, hxz,
    hzc, hz40, hzl, hzw, hzc63, hxacc, hx48, hxh, hxw, hzx, hzg, hzt, hinv⟩
  have hc1 : CodeIn64 ((Extracted.program.onlySegments [addVVfn]).link impl) (LibAddTo.program.link impl) := by
    rw [LibAddTo.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hc2 : CodeIn64 ((Extracted.program.onlySegments [addVWfn]).link impl) (LibAddTo.program.link impl) := by
    rw [LibAddTo.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hVV' := AddVVHyp.live (Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc1 hVV) R b L
  have hVW' := fun b L => Ensures.toSummaryRegs7 (hVW b L) (A64.noExit_restrict64 hap [addVWfn]) hc2
  clear hc1 hc2 hVV hVW
  janus64_intro hs
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hfs : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  simp only [Outside, and_true] at hzw hxw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4232 ∨ (s.regs 4).toNat + 48 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48)],
      (s.regs 4).toNat - 4232 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 48 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  by_cases hx0 : xl.toNat = 0
  · janus64_run [hfs] calls [hVV', hVW']
    refine ⟨?_, L, b, LiveExt.refl R L, Nat.le_refl _, by janus_live, ?_, ?_⟩
    · simp only [natVal_zero, Nat.add_zero]; exact (Nat.mod_eq_of_lt (natVal_lt _ _ _)).symm
    · simp only [List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48)]) ?_ hLs' hwin
      simp only [List.cons_append, List.nil_append]; janus_frame
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hap := hzx (by omega)
  have hzx1 : zp.toNat = xp.toNat ∨ Apart zp.toNat (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    right; unfold Apart at hap ⊢; omega
  have hza1 : s.mem.accessible zp.toNat (8 * xl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
  have hza2 : s.mem.accessible zp.toNat (8 * xl.toNat) false = true := Janus.Arm64.Memory.accessible_weaken _ hza1
  have hzh' : Held R L zp.toNat (8 * xl.toNat) := hzh.sub (Nat.le_refl _) (by omega)
  have hzg' : Apart zp.toNat (8 * xl.toNat) ((s.regs 14).toNat + 16) 8 := by unfold Apart at hzg ⊢; omega
  have hzt' : Apart zp.toNat (8 * xl.toNat) (s.fsBase.toNat - 8) 8 := by unfold Apart at hzt ⊢; omega
  by_cases hxl : xl.toNat = zl.toNat
  · janus64_run [hfs] calls [hVV', hVW']
    all_goals
      refine ⟨by rw [← hxl]; janus_assumption, L, b, LiveExt.refl R L, Nat.le_refl _, by janus_assumption, ?_, ?_⟩
      · simp only [List.append_assoc, List.cons_append, List.nil_append]; janus_frame
      · refine liveFrame_of_frame (rs := [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48)]) ?_ hLs' hwin
        simp only [List.cons_append, List.nil_append]; janus_frame
  have hlt : xl.toNat < zl.toNat := by omega
  have hmask : ((0#64 - (zc - xl)).sshiftRight 63).toNat = 18446744073709551615 := by
    rw [show 0#64 - (zc - xl) = xl - zc by bv_omega]; exact sshr63_of_lt _ _ (by omega) (by omega)
  have hand : xl.toNat * 8 &&& 18446744073709551615 = xl.toNat * 8 := and_ones64 _ (by omega)
  have hs1 : (18446744073709551616 - xl.toNat + zl.toNat) % 18446744073709551616 = zl.toNat - xl.toNat :=
    sub_mod64 _ _ (by omega) zl.isLt
  have hs2 : (18446744073709551616 - xl.toNat + zc.toNat) % 18446744073709551616 = zc.toNat - xl.toNat :=
    sub_mod64 _ _ (by omega) zc.isLt
  have hmod : (zp.toNat + xl.toNat * 8) % 18446744073709551616 = zp.toNat + 8 * xl.toNat := by
    rw [mod64_of_lt _ (by omega)]; omega
  have hzh2 : InRanges (zp.toNat + 8 * xl.toNat) (8 * (zl.toNat - xl.toNat)) L ∨
      Outside (zp.toNat + 8 * xl.toNat) (8 * (zl.toNat - xl.toNat)) R.rt :=
    hzh.sub (by omega) (by omega)
  have hzb1 : s.mem.accessible (zp.toNat + 8 * xl.toNat) (8 * (zl.toNat - xl.toNat)) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hzacc (by omega) (by omega)
  have hzb2 := Janus.Arm64.Memory.accessible_weaken _ hzb1
  have hzal2 : (zp.toNat + 8 * xl.toNat) % 8 = 0 := by omega
  have hLsW : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ (s.regs 4).toNat - 96 - 4136 ∨ (s.regs 4).toNat - 96 + 40 ≤ r.fst := by
    intro r hr; have := hLs' r hr; omega
  have hsplit : ∀ m : Memory, natVal m zp.toNat zl.toNat =
      natVal m zp.toNat xl.toNat + 2 ^ (64 * xl.toNat) * natVal m (zp.toNat + 8 * xl.toNat) (zl.toNat - xl.toNat) := by
    intro m; have := natVal_add m zp.toNat xl.toNat (zl.toNat - xl.toNat)
    rwa [Nat.add_sub_cancel' hxz] at this
  have hB : 0 < 2 ^ (64 * xl.toNat) := Nat.pow_pos (by omega)
  have e16 : (s.regs 4).toNat - 96 + 80 = (s.regs 4).toNat - 16 := by omega
  janus64_run [win, hfs, hmask, hand, hs1, hs2, hmod] calls [hVV', hVW']
  · -- no carry out of `addVV`
    rename_i w _ _ hv hc hfr hinvw hg _
    try rw [e16] at hc
    have hF : MemFrame s.mem w [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48),
        (zp.toNat, zp.toNat + 8 * xl.toNat)] := by janus_frame
    have hhi : natVal w (zp.toNat + 8 * xl.toNat) (zl.toNat - xl.toNat) =
        natVal s.mem (zp.toNat + 8 * xl.toNat) (zl.toNat - xl.toNat) :=
      hF.readLE _ _ (by simp only [Outside, and_true]; omega)
    have hq0 : (natVal s.mem zp.toNat xl.toNat + natVal s.mem xp.toNat xl.toNat) / 2 ^ (64 * xl.toNat) = 0 :=
      hc.symm.trans (by janus_assumption)
    have hlt' : natVal s.mem zp.toNat xl.toNat + natVal s.mem xp.toNat xl.toNat < 2 ^ (64 * xl.toNat) := by
      refine Nat.lt_of_not_le fun h => ?_
      have := Nat.div_pos h hB; omega
    have hv' : natVal w zp.toNat xl.toNat = natVal s.mem zp.toNat xl.toNat + natVal s.mem xp.toNat xl.toNat := by
      rw [hv]; exact Nat.mod_eq_of_lt hlt'
    have hb := natVal_lt w zp.toNat zl.toNat
    rw [hsplit, hv', hhi] at hb
    refine ⟨?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinvw, ?_, ?_⟩
    · rw [hsplit, hsplit s.mem, hv', hhi, Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48)]) ?_ hLs' hwin
      simp only [List.cons_append, List.nil_append]; janus_frame
  · -- carry: `addVW(z[n:], z[n:], 1)`
    rename_i w _ _ hv hc hfr hinvw hg _ hc0 hpc hsp hfp hg14 hx15 L' b' hext hbb hres hv2 hinv2 hF2 hLF2
    try rw [e16] at hc
    have hF : MemFrame s.mem w [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48),
        (zp.toNat, zp.toNat + 8 * xl.toNat)] := by janus_frame
    have hF2' : MemFrame w s'.mem (R.rt ++ [((s.regs 4).toNat - 4232, (s.regs 4).toNat - 56)] ++
        [(zp.toNat + 8 * xl.toNat, zp.toNat + 8 * xl.toNat + 8 * (zl.toNat - xl.toNat))]) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    have hpush : Outside ((s.regs 4).toNat - 96) 8 L := outside_of_forall fun r hr => by
      have := hLs' r hr; omega
    have hLF2' : LiveFrame w s'.mem L [(zp.toNat + 8 * xl.toNat, zp.toNat + 8 * xl.toNat + 8 * (zl.toNat - xl.toNat))] :=
      LiveFrame.trans (LiveFrame.writeLE (LiveFrame.refl w L _) _ hpush) hLF2 (fun _ _ h => h)
    have hlow : natVal s'.mem zp.toNat xl.toNat = natVal w zp.toNat xl.toNat := by
      refine Held.readLE2 hzh' hF2' hLF2' ?_ ?_
      · simp only [Outside, and_true]; omega
      · simp only [Outside, and_true]; omega
    refine ⟨?_, L', b', hext, hbb, hinv2, ?_, ?_⟩
    · rw [hsplit s'.mem, hlow, hv, hv2, hc, split_mod, Nat.add_sub_cancel' hxz, hsplit s.mem]
      unfold natVal
      congr 1; omega
    · simp only [List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine LiveFrame.trans (liveFrame_of_frame (rs := [((s.regs 4).toNat - 4232, (s.regs 4).toNat + 48)]) ?_ hLs' hwin)
        (LiveFrame.mono_ws hLF2' fun a n h => ?_) (fun _ _ h => h)
      · refine hF.mono fun a n h => ?_
        simp only [List.cons_append, List.nil_append, Outside, and_true] at h ⊢; omega
      · simp only [Outside, and_true] at h ⊢; omega

end FvModexp.Amd64.AddTo
