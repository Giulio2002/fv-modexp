import FvModexp.Proofs.Amd64.Top.RunIfaceMono
import FvModexp.Proofs.Amd64.Nat.Callees

set_option autoImplicit false

/-! # `Run` (amd64): the `(*Int).Mod` / `(*Int).exp` interfaces with the `hasADX` / `natOne` entry facts (agent top s49)

Light copies (Run's segment modules must not import the Mod/exp proofs) of divmc's `IMod.ModSpecA`
(Int/ModFunA.lean: `ModSpec` ∧ `hasADX` readable) and expmc's `IExp.ExpA` / `IExp.ExpSpecA` (Exp/IExpFun.lean:
`ExpSpec` ∧ `hasADX` readable ∧ `natOne`'s word apart from `gA`), text verbatim; `Top/RunSucc` bridges them by `rfl`.
Run discharges the extra facts at its calls from `Spec.RunAmd64.CpuOne` (Top/RunC2Cpu). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.RunIface

/-- = `IMod.ModSpecA` -/
def ModSpecA (impl : List Janus.Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesMod).link impl) (segAddr Extracted.program (P ++ "(*Int).Mod"))
      [z, z, y]
      (fun s => (IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above) ∧
        ModX s.mem z.toNat) ∧ s.mem.accessible Callees.adxAddr 1 false = true)
      (fun s s' => s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
        IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

/-- = `IExp.ExpA` -/
def ExpA (m : Janus.Arm64.Memory) : Prop :=
  m.accessible Callees.adxAddr 1 false = true ∧ Apart (m.readLE natOneA 8) 8 gA 32

/-- = `IExp.ExpSpecA` -/
def ExpSpecA (impl : List Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesExp).link impl)
      (segAddr Extracted.program (P ++ "(*Int).exp")) [z, z, y, mm, 0#64]
      (fun s => (IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R s.mem (win s stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 wbA 4 ∧ ModX s.mem z.toNat) ∧
        ExpA s.mem)
      (fun s s' => s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s')

theorem ModSpecA.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpecA impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ModSpecA impl R k' a' := fun b L z y =>
  (h b L z y).mono (fun _ ⟨⟨hp, h1, h2, h3, h4, h5⟩, hx⟩ =>
    ⟨⟨intPre_mono hk ha hp, h1, h2, h3, poolG_mono hk ha h4, h5⟩, hx⟩) fun _ _ _ ⟨hfs, hdf, h0, h1, h2⟩ =>
    ⟨hfs, hdf, h0, intPost_mono hk ha h1, h2⟩

theorem ExpSpecA.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : ExpSpecA impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ExpSpecA impl R k' a' := fun b L z y mm =>
  (h b L z y mm).mono (fun _ ⟨⟨hp, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hx⟩ =>
    ⟨⟨intPre_mono hk ha hp, h1, h2, h3, h4, oneG_mono hk ha h5, poolG_mono hk ha h6, h7, h8, h9⟩, hx⟩)
    fun _ _ _ ⟨hfs, hdf, h0, h1⟩ =>
    ⟨hfs, hdf, h0, intPost_mono hk ha h1⟩

end FvModexp.Amd64.RunIface
