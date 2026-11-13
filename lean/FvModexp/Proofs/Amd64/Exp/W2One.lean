import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W2OneDefs
import FvModexp.Proofs.Amd64.Exp.W2PowDefs

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `one` for `n ≤ 4` (nat.go:1541-1542), `var powers [4]nat` (nat.go:1545) and the call
setup of `buf := stk.nat(5n)` (nat.go:1549; agent expmc s61)

`oneSmall`: from the RR join `rrJ` (spills of `RR` / `zz`) through the frame buffer `one = sp + 0x150` (two
`MOVUPS X15`, `one[0] = 1`), the `powers` zeroing (six `MOVUPS`) to the entry of `(*stack).nat`
(`RSP = sp - 8`, return address `p01`, `AX = st`, `BX = 5n` read from the entry spill `0x148`) with `OnePost`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

/-- entry of `(*stack).nat` -/
abbrev snE : Nat := 6186112

theorem subE8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- the slot facts `rrJ → snE` adds (spills and the return address) -/
@[reducible] def OneSl (sp rrp rrl rrc zzp zzc : Nat) (M : Memory) : Prop :=
  M.readLE (sp + 0x220) 8 = rrp ∧ M.readLE (sp + 0x100) 8 = rrc ∧ M.readLE (sp + 0xf8) 8 = rrl ∧
  M.readLE (sp + 0xa0) 8 = zzc ∧ M.readLE (sp + 0x190) 8 = zzp ∧ M.readLE (sp - 8) 8 = p01

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem oneSmall (impl : List Amd64.Segment) {R : RtInv} {ret : W64} {Q : State → Prop}
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n st rrp rrl rrc zzp zzc : Nat} {M : Memory} {r5 : W64}
    (he : Env R L g fs sp M) (hn : 0 < n) (hn4 : n ≤ 4)
    (hrr : rrp < 2 ^ 64) (hrl : rrl < 2 ^ 64) (hrc : rrc < 2 ^ 64) (hzp : zzp < 2 ^ 64) (hzc : zzc < 2 ^ 64)
    (s3b0 : M.readLE (sp + 0x298) 8 = n) (s148 : M.readLE (sp + 0x148) 8 = 5 * n) (s3d8 : M.readLE (sp + 0x2c0) 8 = st)
    (hacc3 : M.accessible (sp + 0x2c0) 8 false = true)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 rrJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 rrp) (h1 : S.regs 1 = BitVec.ofNat 64 rrl)
    (h8 : S.regs 8 = BitVec.ofNat 64 rrc) (h2 : S.regs 2 = BitVec.ofNat 64 zzc) (h6 : S.regs 6 = BitVec.ofNat 64 zzp)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KA : ∀ (S' : State) (onep : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) → S'.regs 0 = BitVec.ofNat 64 st →
      S'.regs 3 = BitVec.ofNat 64 (5 * n) → S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      OnePost R L L' b b' g fs sp n M S'.mem onep → OneSl sp rrp rrl rrc zzp zzc S'.mem →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hn16 : n ≤ 2 ^ 16 := by omega
  janus64_run [s3b0, s148, s3d8] until [6186112]
  refine KA _ (sp + 0x150) L b rfl ?_ ?_ ?_ ?_ ?_ hfs ?_ rfl ⟨?env, LiveExt.refl R L, by
    simp only [show ¬ 4 < n by omega, ite_false]; omega, ?mf, ?lf, ?inv, ?rg, ?r328, ?one, Or.inl ⟨rfl, hn4⟩⟩ ?sl
  case mf =>
    refine MemFrame.widen ?_ R.rt
    repeat (refine ow_mf ?_ _ (by omega))
    exact MemFrame.refl _ _
  case lf =>
    repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  case env =>
    refine Env.frame he ?_ (out_of_in hgw (ow sp) (ow_in sp)) (out_of_in hfw (ow sp) (ow_in sp)) (LiveExt.refl R L)
    refine MemFrame.widen ?_ R.rt
    repeat (refine ow_mf ?_ _ (by omega))
    exact MemFrame.refl _ _
  case inv =>
    refine FvModexp.Expmc.inv_frame (ws := ow sp) ?_ (ow_out hwrt) hinv
    repeat (refine ow_mf ?_ _ (by omega))
    exact MemFrame.refl _ _
  case rg => simp only [Arm64.Memory.regions_writeLE]
  case r328 =>
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      Nat.reducePow]
    omega
  case one =>
    refine one_val _ _ n hn ?_ (fun j hj => ?_)
    · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
        Nat.reducePow, Nat.one_mod]
    · rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      all_goals simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint,
        Arm64.Memory.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul]
  case sl =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      Nat.reducePow]
    all_goals omega
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals first | exact subE8 (by omega) (by omega) | exact h5 | exact h14 | exact hx15 | rfl

end FvModexp.Amd64.W2Pro
