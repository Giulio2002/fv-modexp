import FvModexp.Proofs.Amd64.Top.RunC2Lem2
import FvModexp.Proofs.Amd64.Top.LibRun
import FvModexp.Proofs.Amd64.Top.RunModX
import FvModexp.Proofs.Amd64.Top.RunIfaceA

set_option autoImplicit false

/-!
# `Run` (amd64): the compute callees as summaries with a precondition fixed in advance (twin of the arm64 `RunC2Sum`)

`janus64_run` proves a callee summary's precondition at the call site. The `IntPre` of `Mod`/`exp`/`Bytes` is large, so
the wrappers here ask only for the callee entry state's `RSP`, memory, `R14`, `fsBase` to be the ones `IntPre` was proved
for (outside the run), the ABI facts (`X15 = 0`, `DF = 0`) and the argument registers to hold the given objects. The
return-address fact is a premise about the fixed memory (`hRA`), proved once per return site (`RunC2RA`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem sub_of_all {ns ms : List String} (h : ns.all (fun x => ms.contains x) = true) :
    ∀ y, ns.contains y = true → ms.contains y = true := by
  intro y hy
  rw [List.all_eq_true] at h
  exact h y (List.contains_iff_mem.1 hy)

/-- `ns ⊆ ms` from a list of positions: the `k`-th name of `ns` is `ms[is[k]]`. The kernel then compares each name
once (`contains` compared it with every earlier entry of `ms`, ~50 shared prefix bytes each: 46 s for the two lists;
asm s84). -/
def subIdx (ms : List String) : List String → List Nat → Bool
  | [], _ => true
  | y :: ns, i :: is => (ms[i]? == some y) && subIdx ms ns is
  | _ :: _, [] => false

theorem sub_of_subIdx {ms : List String} : ∀ {ns : List String} {is : List Nat}, subIdx ms ns is = true →
    ∀ y, ns.contains y = true → ms.contains y = true
  | [], _, _, y, hy => by simp at hy
  | _ :: _, [], h, _, _ => by simp [subIdx] at h
  | x :: ns, i :: is, h, y, hy => by
    simp only [subIdx, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.contains_iff_mem.1 hy with _ | ⟨_, hy'⟩
    · exact List.contains_iff_mem.2 (List.mem_of_getElem? h.1)
    · exact sub_of_subIdx h.2 y (List.contains_iff_mem.2 hy')

set_option maxRecDepth 20000 in
theorem subMod : ∀ y, RunIface.namesMod.contains y = true → LibRun.names.contains y = true :=
  sub_of_subIdx (is := [8, 3, 6, 7, 51, 31, 63, 58, 28, 29, 54, 55, 79, 43, 61, 57, 81, 56, 80, 44, 62, 14, 15, 13, 66, 46, 78, 27, 69, 45, 77, 26, 33, 71, 72, 53, 32, 70, 12, 47, 24, 25]) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem subExp : ∀ y, RunIface.namesExp.contains y = true → LibRun.names.contains y = true :=
  sub_of_subIdx (is := [8, 17, 52, 16, 3, 9, 6, 10, 7, 5, 30, 51, 31, 63, 58, 28, 29, 54, 55, 79, 60, 43, 61, 50, 57, 81, 56, 80, 48, 49, 44, 62,
    14, 15, 13, 66, 46, 78, 27, 69, 45, 77, 26, 11, 65, 23, 68, 21, 35, 74, 34, 73, 22, 37, 76, 36, 75, 20, 39, 41, 59, 33, 71,
    72, 53, 19, 67, 38, 18, 32, 70, 12, 40, 42, 47, 24, 25]) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem subBytes : ∀ y, [RunIface.fnBytes].contains y = true → LibRun.names.contains y = true :=
  sub_of_all (by decide +kernel)

open RunIface in
/-- `z.Mod(z, y)` at a call state with entry `RSP = sp0`, memory `M`, `R14 = g`, `fsBase = fs`. -/
theorem modW (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hM : ModSpecA impl R stkM aboveM) (b1 : Nat) (L1 : List (Nat × Nat)) (sp0 g fs : BitVec 64)
    (M : Janus.Arm64.Memory) (zA yA : Nat)
    (hRA : RetAddr ((Extracted.program.onlySegments namesMod).link impl) (M.readLE sp0.toNat 8))
    (hIP : ∀ t : State, t.regs 4 = sp0 → t.mem = M → t.regs 14 = g → t.fsBase = fs →
      IntPre R b1 (ModBudget (max (lenW M zA) (lenW M yA))) L1 stkM aboveM [zA, yA] t)
    (hy0 : 0 < IntV M yA) (hzl : IntLenLe M zA maxW) (hyl : IntLenLe M yA maxW)
    (hPool : ∀ t : State, t.regs 4 = sp0 → PoolG R M (win t stkM aboveM)) (hX : ModX M zA)
    (hadx : M.accessible Callees.adxAddr 1 false = true) (z y : BitVec 64) :
    Summary (LibRun.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod")
      (fun t => t.xmm 15 = 0 ∧ ArgsFrom64 t 0 [z, z, y] ∧ t.df = false ∧ t.regs 4 = sp0 ∧ t.mem = M ∧
        t.regs 14 = g ∧ t.fsBase = fs ∧ z.toNat = zA ∧ y.toNat = yA)
      (fun t t' => ((t'.regs 4 = t.regs 4 + 8 ∧ t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) ∧
        t'.fsBase = t.fsBase ∧ t'.df = t.df ∧ t'.regs 0 = z ∧
        IntPost R b1 (ModBudget (max (lenW M zA) (lenW M yA))) L1 stkM aboveM zA (IntV M zA % IntV M yA) t t' ∧
        IntV t'.mem yA = IntV M yA) ∧ t'.mem.regions = t.mem.regions) := by
  have hS := LibRun.eq_only ▸ Ensures.toSummaryIn (hM b1 L1 z y) (FvModexp.A64.noExit_restrict64 hap _)
    (by simp [numIntRegs]) (FvModexp.A64.codeIn_restrict_mono64 hap subMod)
  refine Summary.mono hS.regions ?_ ?_
  · rintro t ⟨hx, ha, hdf, hsp, hm, h14, hfs, hz, hy⟩
    subst hz hy
    refine ⟨by rw [hm, hsp]; exact hRA, hx, ha, hdf, ⟨by rw [hm]; exact hIP t hsp hm h14 hfs, by rw [hm]; exact hy0,
      by rw [hm]; exact hzl, by rw [hm]; exact hyl, by rw [hm]; exact hPool t hsp, by rw [hm]; exact hX⟩,
      by rw [hm]; exact hadx⟩
  · rintro t t' ⟨-, -, -, -, hm, -, -, hz, hy⟩ ⟨⟨hcs, hfs, hdf, h0, hpost, hyv⟩, hreg⟩
    subst hz hy
    rw [hm] at hpost hyv
    exact ⟨⟨hcs, hfs, hdf, h0, hpost, hyv⟩, hreg⟩

/-- the two `ExpSpec` pre facts of Run's exp call (`z` = Run's frame slot `RSP - 136`, `m` = `RSP - 200`): `m ≠ nil`, and
`z`'s header apart from the write-barrier flag (`Globals`: the flag is outside Run's window) -/
theorem expX_ops {sp W : Nat} (hb : W ≤ sp) (hW : 4800 ≤ W) (hw : Outside RunIface.wbA 4 [(sp - W, sp + 40)]) :
    sp - 200 ≠ 0 ∧ Apart (sp - 136) 32 RunIface.wbA 4 := by
  simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hw
  exact ⟨by omega, by unfold Apart; omega⟩

open RunIface in
/-- `z.exp(z, y, mm, false)` at a call state with entry `RSP = sp0`, memory `M`, `R14 = g`, `fsBase = fs`. -/
theorem expW (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : ExpSpecA impl R stkM aboveM) (b1 : Nat) (L1 : List (Nat × Nat)) (sp0 g fs : BitVec 64)
    (M : Janus.Arm64.Memory) (zA yA mA : Nat)
    (hRA : RetAddr ((Extracted.program.onlySegments namesExp).link impl) (M.readLE sp0.toNat 8))
    (hIP : ∀ t : State, t.regs 4 = sp0 → t.mem = M → t.regs 14 = g → t.fsBase = fs →
      IntPre R b1 (ExpBudget (max (max (lenW M zA) (lenW M yA)) (lenW M mA)) (lenW M yA)) L1 stkM aboveM
        [zA, yA, mA] t)
    (hm0 : 0 < IntV M mA) (hzl : IntLenLe M zA maxW) (hyl : IntLenLe M yA maxW) (hml : IntLenLe M mA maxW)
    (hOne : ∀ t : State, t.regs 4 = sp0 → OneG R L1 M (win t stkM aboveM) [zA, yA, mA])
    (hPool : ∀ t : State, t.regs 4 = sp0 → PoolG R M (win t stkM aboveM)) (hmA0 : mA ≠ 0) (hzwb : Apart zA 32 wbA 4)
    (hzX : ModX M zA) (hxa : ExpA M) (z y mm : BitVec 64) :
    Summary (LibRun.program.link impl)
      (segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).exp")
      (fun t => t.xmm 15 = 0 ∧ ArgsFrom64 t 0 [z, z, y, mm, 0#64] ∧ t.df = false ∧ t.regs 4 = sp0 ∧ t.mem = M ∧
        t.regs 14 = g ∧ t.fsBase = fs ∧ z.toNat = zA ∧ y.toNat = yA ∧ mm.toNat = mA)
      (fun t t' => ((t'.regs 4 = t.regs 4 + 8 ∧ t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) ∧
        t'.fsBase = t.fsBase ∧ t'.df = t.df ∧ t'.regs 0 = z ∧
        IntPost R b1 (ExpBudget (max (max (lenW M zA) (lenW M yA)) (lenW M mA)) (lenW M yA)) L1 stkM aboveM zA
          (IntV M zA ^ IntV M yA % IntV M mA) t t') ∧ t'.mem.regions = t.mem.regions) := by
  have hS := LibRun.eq_only ▸ Ensures.toSummaryIn (hE b1 L1 z y mm) (FvModexp.A64.noExit_restrict64 hap _)
    (by simp [numIntRegs]) (FvModexp.A64.codeIn_restrict_mono64 hap subExp)
  refine Summary.mono hS.regions ?_ ?_
  · rintro t ⟨hx, ha, hdf, hsp, hm, h14, hfs, hz, hy, hmm⟩
    subst hz hy hmm
    refine ⟨by rw [hm, hsp]; exact hRA, hx, ha, hdf, ⟨by rw [hm]; exact hIP t hsp hm h14 hfs, by rw [hm]; exact hm0,
      by rw [hm]; exact hzl, by rw [hm]; exact hyl, by rw [hm]; exact hml, by rw [hm]; exact hOne t hsp,
      by rw [hm]; exact hPool t hsp, hmA0, hzwb, by rw [hm]; exact hzX⟩, by rw [hm]; exact hxa⟩
  · rintro t t' ⟨-, -, -, -, hm, -, -, hz, hy, hmm⟩ ⟨⟨hcs, hfs, hdf, h0, hpost⟩, hreg⟩
    subst hz hy hmm
    rw [hm] at hpost
    exact ⟨⟨hcs, hfs, hdf, h0, hpost⟩, hreg⟩

open RunIface in
/-- `x.Bytes()` at a call state with entry `RSP = sp0`, memory `M`, `R14 = g`, `fsBase = fs`. -/
theorem bytesW (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hB : BytesSpec impl R stkM aboveM) (b1 : Nat) (L1 : List (Nat × Nat)) (sp0 g fs : BitVec 64)
    (M : Janus.Arm64.Memory) (xA : Nat)
    (hRA : RetAddr ((Extracted.program.onlySegments [fnBytes]).link impl) (M.readLE sp0.toNat 8))
    (hIP : ∀ t : State, t.regs 4 = sp0 → t.mem = M → t.regs 14 = g → t.fsBase = fs →
      IntPre R b1 (BytesBudget (lenW M xA)) L1 stkM aboveM [xA] t)
    (hxl : IntLenLe M xA maxW) (x : BitVec 64) :
    Summary (LibRun.program.link impl) (segAddr Extracted.program fnBytes)
      (fun t => t.xmm 15 = 0 ∧ ArgsFrom64 t 0 [x] ∧ t.df = false ∧ t.regs 4 = sp0 ∧ t.mem = M ∧ t.regs 14 = g ∧
        t.fsBase = fs ∧ x.toNat = xA)
      (fun t t' => ((t'.regs 4 = t.regs 4 + 8 ∧ t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) ∧
        t'.fsBase = t.fsBase ∧ t'.df = t.df ∧
        ∃ p n c : Nat, (t'.regs 0).toNat = p ∧ (t'.regs 3).toNat = n ∧ (t'.regs 1).toNat = c ∧ n ≤ c ∧
          beVal t'.mem p n = IntV M xA ∧ (n = 0 ∨ (t'.mem.bytes p).toNat ≠ 0) ∧
          ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L1 L' ∧ b1 - BytesBudget (lenW M xA) ≤ b' ∧
            R.inv b' L' g.toNat (view R.rt L' t'.mem) ∧ (0 < n → InRanges p n L' ∧ InRanges p n R.rt ∧
              ApartAll p n L1 ∧ t'.mem.accessible p n true = true ∧ p + n ≤ 2 ^ 48) ∧
            MemFrame M t'.mem (R.rt ++ win t stkM aboveM) ∧ LiveFrame M t'.mem L1 []) ∧
        t'.mem.regions = t.mem.regions) := by
  have hS := LibRun.eq_only ▸ Ensures.toSummaryIn (hB b1 L1 x) (FvModexp.A64.noExit_restrict64 hap _)
    (by simp [numIntRegs]) (FvModexp.A64.codeIn_restrict_mono64 hap subBytes)
  refine Summary.mono hS.regions ?_ ?_
  · rintro t ⟨hx0, ha, hdf, hsp, hm, h14, hfs, hx⟩
    subst hx
    exact ⟨by rw [hm, hsp]; exact hRA, hx0, ha, hdf, by rw [hm]; exact hIP t hsp hm h14 hfs, by rw [hm]; exact hxl⟩
  · rintro t t' ⟨-, -, -, -, hm, h14, -, hx⟩ ⟨⟨hcs, hfs, hdf, hpost⟩, hreg⟩
    subst hx
    rw [hm, h14] at hpost
    exact ⟨⟨hcs, hfs, hdf, hpost⟩, hreg⟩

end FvModexp.Amd64.Run
