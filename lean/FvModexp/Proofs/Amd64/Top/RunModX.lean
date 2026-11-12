import FvModexp.Proofs.Amd64.Top.RunIfaceMono

set_option autoImplicit false

/-! # `Run` (amd64): the FINAL `(*Int).Mod` interface `ModSpecM` = `RunIface.ModSpec` + `ModX` (agent top s21)

Twin of the arm64 `Top/RunModX` (divmc s28 request): `ModX m z` = `z`'s array (when it has one) apart from the threshold
globals at `RunIface.gA`; `ModSpecM` = `ModSpec` with it as the LAST pre conjunct. NEW module instead of a `RunIface` edit
(REBUILD COST rule). Run discharges `ModX` in RunC2M (OpDone's fresh array, `Globals`' `Outside gA 32 R.rt`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.RunIface

/-- `z`'s array (when it has one) is apart from the threshold globals -/
def ModX (m : Janus.Arm64.Memory) (z : Nat) : Prop :=
  0 < m.readLE (z + 24) 8 → Apart (m.readLE (z + 8) 8) (8 * m.readLE (z + 24) 8) gA 32

/-- **`z.Mod(z, y)`** as Run calls it: `ModSpec` with `ModX` as the last precondition conjunct -/
def ModSpecM (impl : List Janus.Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesMod).link impl) (segAddr Extracted.program (P ++ "(*Int).Mod")) [z, z, y]
      (fun s => IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above) ∧
        ModX s.mem z.toNat)
      (fun s s' => s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
        IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

/-- the old interface is the stronger one -/
theorem ModSpecM.of_modSpec {impl : List Janus.Amd64.Segment} {R : RtInv} {k a : Nat} (h : ModSpec impl R k a) :
    ModSpecM impl R k a := fun b L z y =>
  (h b L z y).mono (fun _ ⟨hp, h1, h2, h3, h4, _⟩ => ⟨hp, h1, h2, h3, h4⟩) fun _ _ _ h => h

theorem ModSpecM.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpecM impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ModSpecM impl R k' a' := fun b L z y =>
  (h b L z y).mono (fun _ ⟨hp, h1, h2, h3, h4, h5⟩ => ⟨intPre_mono hk ha hp, h1, h2, h3, poolG_mono hk ha h4, h5⟩)
    fun _ _ _ ⟨hfs, hdf, h0, h1, h2⟩ => ⟨hfs, hdf, h0, intPost_mono hk ha h1, h2⟩

end FvModexp.Amd64.RunIface
