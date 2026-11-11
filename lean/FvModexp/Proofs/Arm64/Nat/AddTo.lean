import FvModexp.Proofs.Arm64.Nat.LibAddTo
import FvModexp.Proofs.Arm64.Nat.AsmCallees
import FvModexp.Proofs.Arm64.Nat.AddVW
import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.DivmcBits

/-!
# `addTo(z, x nat)` (go-bigmodexpfix nat.go:234), arm64

```go
func addTo(z, x nat) {
	if n := len(x); n > 0 {
		if c := addVV(z[:n], z[:n], x[:n]); c != 0 {
			if n < len(z) {
				addVW(z[n:], z[n:], c)
			}
		}
	}
}
```
`z += x` in place over `len z` limbs (the carry out of `z[len z - 1]` is dropped). Frame 96 (`MOVD.W R30, -96(RSP)`),
spills `X0..X5` at `SP + 8 … SP + 48` (`above = 48`); deepest callee `addVW` (`stk 4144`): `stk = 96 + 4144 = 4240`.
`addVV.abi0` takes its frame at `SP' + 8 … SP' + 88` of addTo's frame `SP' = SP - 96`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.AddTo

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addTo"
def names : List String := LibAddTo.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc]
      (fun s => CallEnv R L s 4240 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
        NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4240 48) ∧ zc.toNat < 2 ^ 63 ∧
        s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
        Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4240 48) ∧
        (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
        Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8 ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
      (fun s s' => natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ winA s 4240 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)]) := by
  rw [show names = LibAddTo.names from rfl, ← LibAddTo.eq_only]
  have hVV := addVVHyp impl hap
  intro ret hret s hs ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, hxz, hzc, hz40, hzl, hzw, hzc63,
    hxacc, hx48, hxh, hxw, hzx, hzg, hinv⟩
  have hc1 : CodeIn ((Extracted.program.onlySegments [addVVfn]).link impl) (LibAddTo.program.link impl) := by
    rw [LibAddTo.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hc2 : CodeIn ((Extracted.program.onlySegments [addVWfn]).link impl) (LibAddTo.program.link impl) := by
    rw [LibAddTo.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hVV' := AddVVHyp.live (Janus.Contracts.EqHashModel.Summary.of_codeIn hc1 hVV) R b L
  have hVW := fun b L zp zl zc xp xl xc y => AddVW.ens impl hap R hmv b L zp zl zc xp xl xc y
  have hVW' := fun b L => Ensures.toSummaryRegs7 (hVW b L) (noExit_restrict hap [addVWfn]) hc2
  clear hc1 hc2 hVV hVW hmv
  janus_intro hs
  simp only [Outside, and_true] at hzw hxw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 48 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ winA s 4240 48, s.sp.toNat - 4240 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 48 := by
    simp only [winA, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  by_cases hx0 : xl.toNat = 0
  · janus_run calls [hVV', hVW']
    refine ⟨?_, L, b, LiveExt.refl R L, Nat.le_refl _, by janus_live, ?_, ?_⟩
    · simp only [natVal_zero, Nat.add_zero]; exact (Nat.mod_eq_of_lt (natVal_lt _ _ _)).symm
    · simp only [winA, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := winA s 4240 48) ?_ hLs' hwin
      simp only [winA, List.cons_append, List.nil_append]; janus_frame
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hap := hzx (by omega)
  have hzx1 : zp.toNat = xp.toNat ∨ Apart zp.toNat (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    right; unfold Apart at hap ⊢; omega
  have hzr : zp.toNat + 8 * xl.toNat ≤ s.sp.toNat - 96 + 80 ∨ s.sp.toNat - 96 + 80 + 8 ≤ zp.toNat := by omega
  have hza1 : s.mem.accessible zp.toNat (8 * xl.toNat) true = true :=
    Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
  have hza2 : s.mem.accessible zp.toNat (8 * xl.toNat) false = true := Memory.accessible_weaken _ hza1
  have hzh' : Held R L zp.toNat (8 * xl.toNat) := hzh.sub (Nat.le_refl _) (by omega)
  have hzg' : Apart zp.toNat (8 * xl.toNat) ((s.regs 28).toNat + 16) 8 := by unfold Apart at hzg ⊢; omega
  have e16 : s.sp.toNat - 96 + 80 = s.sp.toNat - 16 := by omega
  by_cases hxl : xl.toNat = zl.toNat
  · janus_run calls [hVV', hVW']
    all_goals
      refine ⟨by rw [← hxl]; janus_assumption, L, b, LiveExt.refl R L, Nat.le_refl _, by janus_assumption, ?_, ?_⟩
      · simp only [winA, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
      · refine liveFrame_of_frame (rs := winA s 4240 48) ?_ hLs' hwin
        simp only [winA, List.cons_append, List.nil_append]; janus_frame
  have hlt : xl.toNat < zl.toNat := by omega
  have hmask : ((xl - zc).sshiftRight 63).toNat = 18446744073709551615 := sshr63_of_lt _ _ (by omega) (by omega)
  have hand : xl.toNat &&& 18446744073709551615 = xl.toNat := and_ones64 _ xl.isLt
  have hs1 : (18446744073709551616 - xl.toNat + zl.toNat) % 18446744073709551616 = zl.toNat - xl.toNat :=
    sub_mod64 _ _ (by omega) zl.isLt
  have hs2 : (18446744073709551616 - xl.toNat + zc.toNat) % 18446744073709551616 = zc.toNat - xl.toNat :=
    sub_mod64 _ _ (by omega) zc.isLt
  have hmod : (zp.toNat + 8 * xl.toNat) % 18446744073709551616 = zp.toNat + 8 * xl.toNat :=
    mod64_of_lt _ (by omega)
  have hzh2 : InRanges (zp.toNat + 8 * xl.toNat) (8 * (zl.toNat - xl.toNat)) L ∨
      Outside (zp.toNat + 8 * xl.toNat) (8 * (zl.toNat - xl.toNat)) R.rt :=
    hzh.sub (by omega) (by omega)
  have hzb1 : s.mem.accessible (zp.toNat + 8 * xl.toNat) (8 * (zl.toNat - xl.toNat)) true = true :=
    Memory.accessible_mono _ hzacc (by omega) (by omega)
  have hzb2 := Memory.accessible_weaken _ hzb1
  have hLsW : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 96 - 4144 ∨ s.sp.toNat - 96 + 40 ≤ r.fst := by
    intro r hr; have := hLs' r hr; omega
  -- the value pieces
  have hsplit : ∀ m : Memory, natVal m zp.toNat zl.toNat =
      natVal m zp.toNat xl.toNat + 2 ^ (64 * xl.toNat) * natVal m (zp.toNat + 8 * xl.toNat) (zl.toNat - xl.toNat) := by
    intro m; have := natVal_add m zp.toNat xl.toNat (zl.toNat - xl.toNat)
    rwa [Nat.add_sub_cancel' hxz] at this
  have hlo := natVal_lt s.mem zp.toNat xl.toNat
  have hxv := natVal_lt s.mem xp.toNat xl.toNat
  have hB : 0 < 2 ^ (64 * xl.toNat) := Nat.pow_pos (by omega)
  janus_run [hmask, hand, hs1, hs2, hmod] calls [hVV', hVW']
  · -- no carry out of `addVV`: `z = z + x` exactly
    rename_i w hv hc hfr hinvw hg
    rw [e16] at hc
    have hF : MemFrame s.mem w [(s.sp.toNat - 4240, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48),
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
    · simp only [winA, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := winA s 4240 48) ?_ hLs' hwin
      simp only [winA, List.cons_append, List.nil_append]; janus_frame
  · -- carry: `addVW(z[n:], z[n:], 1)`
    rename_i w hv hc hfr hinvw hg hc0 hpc hsp h28 h29 h18 L' b' hext hbb hres hv2 hinv2 hF2 hLF2
    rw [e16] at hc
    have hF : MemFrame s.mem w [(s.sp.toNat - 4240, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48),
        (zp.toNat, zp.toNat + 8 * xl.toNat)] := by janus_frame
    have hlow : natVal s'.mem zp.toNat xl.toNat = natVal w zp.toNat xl.toNat := by
      refine Held.readLE2 hzh' hF2 hLF2 ?_ ?_
      · simp only [Outside, and_true, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · simp only [Outside, and_true]; omega
    refine ⟨?_, L', b', hext, hbb, hinv2, ?_, ?_⟩
    · rw [hsplit s'.mem, hlow, hv, hv2, hc, split_mod, Nat.add_sub_cancel' hxz, hsplit s.mem]
      unfold natVal
      congr 1; omega
    · simp only [winA, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine LiveFrame.trans (liveFrame_of_frame (rs := winA s 4240 48) ?_ hLs' hwin)
        (LiveFrame.mono_ws hLF2 fun a n h => ?_) (fun _ _ h => h)
      · refine hF.mono fun a n h => ?_
        simp only [winA, List.cons_append, List.nil_append, Outside, and_true] at h ⊢; omega
      · simp only [Outside, and_true] at h ⊢; omega

end FvModexp.Arm64.AddTo
