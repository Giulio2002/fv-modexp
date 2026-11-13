import FvModexp.Proofs.Arm64.Top.RunModX

set_option autoImplicit false

/-!
# `RunIface.ModSpec` / `ExpSpec` with LITERAL object names (top s44)

Janus audit round 8 I1: a statement's `segAddr` object names must be string literals. `RunIface.ModSpec`/`ExpSpec` name
the callee as `P ++ "(*Int).Mod"`; the row statements that take them as premises (`Run.correctness_ok`) use these copies
instead, text identical except the literal name. `ModSpecL.toM`/`ExpSpecL.to` (and back) are `id` (definitional: the
strings are equal). Editing `RunIface` itself would rebuild ~1400 modules.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.RunIface

/-- `ModSpec` with the literal name `math/big.(*Int).Mod` -/
def ModSpecL (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesMod).link impl) (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod") [z, z, y]
      (fun s => IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above) ∧
        ModX s.mem z.toNat)
      (fun s s' => s'.regs 0 = z ∧ IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

/-- `ExpSpec` with the literal name `math/big.(*Int).exp` -/
def ExpSpecL (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesExp).link impl) (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).exp")
      [z, z, y, mm, 0#64]
      (fun s => IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat)) (lenW s.mem y.toNat))
        L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R s.mem (win s stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 wbA 4 ∧ ModX s.mem z.toNat)
      (fun s s' => s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat)) (lenW s.mem y.toNat))
          L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s')

theorem ModSpecL.toM {impl : List Segment} {R : RtInv} {k a : Nat} (h : ModSpecL impl R k a) : ModSpecM impl R k a := h
theorem ModSpecL.ofM {impl : List Segment} {R : RtInv} {k a : Nat} (h : ModSpecM impl R k a) : ModSpecL impl R k a := h
theorem ExpSpecL.to {impl : List Segment} {R : RtInv} {k a : Nat} (h : ExpSpecL impl R k a) : ExpSpec impl R k a := h
theorem ExpSpecL.of {impl : List Segment} {R : RtInv} {k a : Nat} (h : ExpSpec impl R k a) : ExpSpecL impl R k a := h

end FvModexp.Arm64.RunIface
