import FvModexp.Proofs.Arm64.Top.RunC2Lem
import FvModexp.Proofs.Arm64.Top.RunCallees2

set_option autoImplicit false

/-!
# `Run` (arm64): the compute callees as summaries with a precondition fixed in advance

`janus_run` proves a callee summary's precondition at the call site. The `IntPre` of `Mod`/`exp`/`Bytes` is large, so
the wrappers here ask only for the call state's `SP`, memory and `X28` to be the ones `IntPre` was proved for (outside the
run, by `RunC2Lem`), and the argument registers to hold the given objects.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

open RunIface in
/-- `z.Mod(z, y)` at a call state with `SP = sp0`, memory `M`, `X28 = g`. -/
theorem modW (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hM : ModSpec impl R stkM aboveM) (b1 : Nat) (L1 : List (Nat × Nat)) (sp0 g : BitVec 64) (M : Memory) (zA yA : Nat)
    (hIP : ∀ t : State, t.sp = sp0 → t.mem = M → t.regs 28 = g →
      IntPre R b1 (ModBudget (max (lenW M zA) (lenW M yA))) L1 stkM aboveM [zA, yA] t)
    (hy0 : 0 < IntV M yA) (hzl : IntLenLe M zA maxW) (hyl : IntLenLe M yA maxW)
    (hPool : ∀ t : State, t.sp = sp0 → PoolG R M (win t stkM aboveM)) (z y : BitVec 64) :
    Summary (LibRun.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod")
      (fun t => RetAddr ((Extracted.program.onlySegments namesMod).link impl) (t.regs 30).toNat ∧
        ArgsFrom t 0 [z, z, y] ∧ t.sp = sp0 ∧ t.mem = M ∧ t.regs 28 = g ∧ z.toNat = zA ∧ y.toNat = yA)
      (fun t t' => ((t'.sp = t.sp ∧ t'.regs 28 = t.regs 28 ∧ t'.regs 29 = t.regs 29 ∧ t'.regs 18 = t.regs 18) ∧
        t'.regs 0 = z ∧ IntPost R b1 (ModBudget (max (lenW M zA) (lenW M yA))) L1 stkM aboveM zA
          (IntV M zA % IntV M yA) t t' ∧ IntV t'.mem yA = IntV M yA) ∧ t'.mem.regions = t.mem.regions) := by
  refine Summary.mono (RunCallees.modSum impl hap R stkM aboveM hM b1 L1 z y).regions ?_ ?_
  · rintro t ⟨hr, ha, hsp, hm, h28, hz, hy⟩
    subst hz hy
    exact ⟨hr, ha, by rw [hm]; exact hIP t hsp hm h28, by rw [hm]; exact hy0, by rw [hm]; exact hzl,
      by rw [hm]; exact hyl, by rw [hm]; exact hPool t hsp⟩
  · rintro t t' ⟨-, -, -, hm, -, hz, hy⟩ ⟨⟨hcs, h0, hpost, hyv⟩, hreg⟩
    subst hz hy
    rw [hm] at hpost hyv
    exact ⟨⟨hcs, h0, hpost, hyv⟩, hreg⟩

/-- the two `ExpSpec` pre facts of Run's exp call (`z` = Run's frame slot `sp - 136`, `m` = `sp - 200`): `m ≠ nil`, and
`z`'s header apart from the write-barrier flag (`Globals`: the flag is outside Run's window) -/
theorem expX_ops {sp W : Nat} (hb : W ≤ sp) (hW : 4800 ≤ W) (hw : Outside RunIface.wbA 4 [(sp - W, sp + 40)]) :
    sp - 200 ≠ 0 ∧ Apart (sp - 136) 32 RunIface.wbA 4 := by
  simp only [outside_cons, outside_nil, and_true] at hw
  exact ⟨by omega, by unfold Apart; omega⟩

open RunIface in
/-- `z.exp(z, y, mm, false)` at a call state with `SP = sp0`, memory `M`, `X28 = g`. -/
theorem expW (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : ExpSpec impl R stkM aboveM) (b1 : Nat) (L1 : List (Nat × Nat)) (sp0 g : BitVec 64) (M : Memory)
    (zA yA mA : Nat)
    (hIP : ∀ t : State, t.sp = sp0 → t.mem = M → t.regs 28 = g →
      IntPre R b1 (ExpBudget (max (max (lenW M zA) (lenW M yA)) (lenW M mA)) (lenW M yA)) L1 stkM aboveM [zA, yA, mA] t)
    (hm0 : 0 < IntV M mA) (hzl : IntLenLe M zA maxW) (hyl : IntLenLe M yA maxW) (hml : IntLenLe M mA maxW)
    (hOne : ∀ t : State, t.sp = sp0 → OneG R L1 M (win t stkM aboveM) [zA, yA, mA])
    (hPool : ∀ t : State, t.sp = sp0 → PoolG R M (win t stkM aboveM)) (hmA0 : mA ≠ 0) (hzwb : Apart zA 32 wbA 4)
    (z y mm : BitVec 64) :
    Summary (LibRun.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).exp")
      (fun t => RetAddr ((Extracted.program.onlySegments namesExp).link impl) (t.regs 30).toNat ∧
        ArgsFrom t 0 [z, z, y, mm, 0#64] ∧ t.sp = sp0 ∧ t.mem = M ∧ t.regs 28 = g ∧ z.toNat = zA ∧ y.toNat = yA ∧
        mm.toNat = mA)
      (fun t t' => ((t'.sp = t.sp ∧ t'.regs 28 = t.regs 28 ∧ t'.regs 29 = t.regs 29 ∧ t'.regs 18 = t.regs 18) ∧
        t'.regs 0 = z ∧ IntPost R b1 (ExpBudget (max (max (lenW M zA) (lenW M yA)) (lenW M mA)) (lenW M yA)) L1 stkM
          aboveM zA (IntV M zA ^ IntV M yA % IntV M mA) t t') ∧ t'.mem.regions = t.mem.regions) := by
  refine Summary.mono (RunCallees.expSum impl hap R stkM aboveM hE b1 L1 z y mm).regions ?_ ?_
  · rintro t ⟨hr, ha, hsp, hm, h28, hz, hy, hmm⟩
    subst hz hy hmm
    exact ⟨hr, ha, by rw [hm]; exact hIP t hsp hm h28, by rw [hm]; exact hm0, by rw [hm]; exact hzl,
      by rw [hm]; exact hyl, by rw [hm]; exact hml, by rw [hm]; exact hOne t hsp,
      by rw [hm]; exact hPool t hsp, hmA0, hzwb⟩
  · rintro t t' ⟨-, -, -, hm, -, hz, hy, hmm⟩ ⟨⟨hcs, h0, hpost⟩, hreg⟩
    subst hz hy hmm
    rw [hm] at hpost
    exact ⟨⟨hcs, h0, hpost⟩, hreg⟩

open RunIface in
/-- `x.Bytes()` at a call state with `SP = sp0`, memory `M`, `X28 = g`. -/
theorem bytesW (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hB : BytesSpec impl R stkM aboveM) (b1 : Nat) (L1 : List (Nat × Nat)) (sp0 g : BitVec 64) (M : Memory) (xA : Nat)
    (hIP : ∀ t : State, t.sp = sp0 → t.mem = M → t.regs 28 = g →
      IntPre R b1 (BytesBudget (lenW M xA)) L1 stkM aboveM [xA] t)
    (hxl : IntLenLe M xA maxW) (x : BitVec 64) :
    Summary (LibRun.program.link impl) (segAddr Extracted.program fnBytes)
      (fun t => RetAddr ((Extracted.program.onlySegments [fnBytes]).link impl) (t.regs 30).toNat ∧
        ArgsFrom t 0 [x] ∧ t.sp = sp0 ∧ t.mem = M ∧ t.regs 28 = g ∧ x.toNat = xA)
      (fun t t' => ((t'.sp = t.sp ∧ t'.regs 28 = t.regs 28 ∧ t'.regs 29 = t.regs 29 ∧ t'.regs 18 = t.regs 18) ∧
        ∃ p n c : Nat, (t'.regs 0).toNat = p ∧ (t'.regs 1).toNat = n ∧ (t'.regs 2).toNat = c ∧ n ≤ c ∧
          beVal t'.mem p n = IntV M xA ∧ (n = 0 ∨ (t'.mem.bytes p).toNat ≠ 0) ∧
          ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L1 L' ∧ b1 - BytesBudget (lenW M xA) ≤ b' ∧
            R.inv b' L' (g.toNat) (view R.rt L' t'.mem) ∧ (0 < n → InRanges p n L' ∧ InRanges p n R.rt ∧
              ApartAll p n L1 ∧ t'.mem.accessible p n true = true ∧ p + n ≤ 2 ^ 48) ∧
            MemFrame M t'.mem (R.rt ++ winA t stkM aboveM) ∧ LiveFrame M t'.mem L1 []) ∧
        t'.mem.regions = t.mem.regions) := by
  refine Summary.mono (RunCallees.bytesSum impl hap R stkM aboveM hB b1 L1 x).regions ?_ ?_
  · rintro t ⟨hr, ha, hsp, hm, h28, hx⟩
    subst hx
    exact ⟨hr, ha, by rw [hm]; exact hIP t hsp hm h28, by rw [hm]; exact hxl⟩
  · rintro t t' ⟨-, -, -, hm, h28, hx⟩ ⟨⟨hcs, hpost⟩, hreg⟩
    subst hx
    rw [hm, h28] at hpost
    exact ⟨⟨hcs, hpost⟩, hreg⟩

end FvModexp.Arm64.Run
