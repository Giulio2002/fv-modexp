import FvModexp.Proofs.Arm64.Top.RunCallees2
import FvModexp.Proofs.Arm64.Top.RunIfaceMono

set_option autoImplicit false

/-! # `Run` (arm64): the FINAL `(*Int).Mod` interface `ModSpecM` = `RunIface.ModSpec` + `ModX` (agent top s21)

divmc s28 ("[divmc s28] REQUEST top", NOTES-conventions): `z.Mod(z, y)` writes the remainder into `z`'s own array, then
`divLarge` / `divRecursiveStep` / `nat.mul` read the threshold globals at `RunIface.gA`; `IntPre`'s `Held` does not put
that array apart from `gA`. `ModX m z` (divmc's `IMod.ModX` body verbatim) is the missing fact; `ModSpecM` is
`ModSpec` with it as the LAST pre conjunct (= divmc's `IMod.ModSpecX` body verbatim, so divmc's proof is one).
Kept in this NEW module instead of editing `RunIface` (REBUILD COST rule); Run discharges `ModX` from `OpDone`'s fresh
array (`InRanges … R.rt`) and `Globals`' `Outside gA 32 R.rt` (RunC2M). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.RunIface

/-- `z`'s array (when it has one) is apart from the threshold globals (divmc's `IMod.ModX`) -/
def ModX (m : Memory) (z : Nat) : Prop :=
  0 < m.readLE (z + 24) 8 → Apart (m.readLE (z + 8) 8) (8 * m.readLE (z + 24) 8) gA 32

/-- **`z.Mod(z, y)`** as Run calls it: `ModSpec` with `ModX` as the last precondition conjunct -/
def ModSpecM (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesMod).link impl) (segAddr Extracted.program (P ++ "(*Int).Mod")) [z, z, y]
      (fun s => IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above) ∧
        ModX s.mem z.toNat)
      (fun s s' => s'.regs 0 = z ∧ IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

/-- the old interface is the stronger one -/
theorem ModSpecM.of_modSpec {impl : List Segment} {R : RtInv} {k a : Nat} (h : ModSpec impl R k a) :
    ModSpecM impl R k a := fun b L z y =>
  (h b L z y).mono (fun _ ⟨hp, h1, h2, h3, h4, _⟩ => ⟨hp, h1, h2, h3, h4⟩) fun _ _ _ h => h

theorem ModSpecM.mono {impl : List Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpecM impl R k a) (hk : k ≤ k')
    (ha : a ≤ a') : ModSpecM impl R k' a' := fun b L z y =>
  (h b L z y).mono (fun _ ⟨hp, h1, h2, h3, h4, h5⟩ => ⟨intPre_mono hk ha hp, h1, h2, h3, poolG_mono hk ha h4, h5⟩)
    fun _ _ _ ⟨h0, h1, h2⟩ => ⟨h0, intPost_mono hk ha h1, h2⟩

end FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.RunCallees

set_option linter.defProp false in
/-- `z.Mod(z, y)` (final interface `ModSpecM`) as a callee of `Run`. -/
def modSumM (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stk above : Nat)
    (hM : RunIface.ModSpecM impl R stk above) :=
  fun (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) =>
    (libRun_eq ▸ Ensures.toSummaryIn (hM b L z y) (noExit_restrict hap _) (codeIn_restrict_full hap _) :
      Summary (LibRun.program.link impl) _ _ _)

end FvModexp.Arm64.RunCallees
