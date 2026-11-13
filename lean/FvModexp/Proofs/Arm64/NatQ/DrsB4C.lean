import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsB4D

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsB4C.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), loop body segment 4 (the call): `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831)

`b4`: from `A3` (`0x1ba684`, after `clear(qhatv)`) → the argument loads → `CALL nat.mul` (`0x1ba6ac`, premise
`MulHypXE` on a library program `ns` inside `LibDrs`) → the stores of the result `qhatv` (`SP'+328/152/168`), `i := 0`
→ the correction loop's head `C` (`0x1ba700`) at the model state `Cx.st0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the call `nat.mul` from its call state `X` (memory = `A3`'s) -/
theorem b4c (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains fn = false)
    (hcode : CodeIn ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    {stkM aboveM : Nat} (hmul : MulHypQE impl R ns stkM aboveM mulCQ) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hA : A3 R c s Lk bk S j Z U qn) (Q : State → Prop)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program EvenHyp.fnMul)) (hm : X.mem = S.mem)
    (hsp : X.sp = s.sp - 400#64) (h0 : X.regs 0 = BitVec.ofNat 64 (c.qv s S.mem))
    (h1 : X.regs 1 = BitVec.ofNat 64 (3 * c.vl)) (h2 : X.regs 2 = BitVec.ofNat 64 (3 * c.vl))
    (h3 : X.regs 3 = BitVec.ofNat 64 c.st) (h4 : X.regs 4 = BitVec.ofNat 64 c.t0) (h5 : X.regs 5 = BitVec.ofNat 64 qn)
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h7 : X.regs 7 = BitVec.ofNat 64 c.vp)
    (h8 : X.regs 8 = BitVec.ofNat 64 (c.vl / 2 - 1)) (h9 : X.regs 9 = BitVec.ofNat 64 c.vc)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 r4)
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 r4 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 → T.regs 0 = BitVec.ofNat 64 (c.qv s S.mem) →
      T.regs 1 = BitVec.ofNat 64 (c.P s j U).length → T.regs 2 = BitVec.ofNat 64 (3 * c.vl) →
      (∃ L' b', Mc R c s L' b' T.mem j Z U (c.qv s S.mem) (c.st0 s j U)) → c.qv s S.mem < 2 ^ 64 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, hvc40, -, ⟨hvl9, -⟩, -, -, -, -, -, ⟨-, -, -, -, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hqle := hA.qle
  have hst48 : c.st + 24 ≤ 2 ^ 48 := hA.ev.sok.2.2.2.1
  have ht48 := hcr.t048
  have hv48 : c.vp + 8 * c.vl ≤ 2 ^ 48 := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hq48 : c.qv s S.mem < 2 ^ 48 := by
    have hl := hA.fp.len; have hlc := hA.ev.sok.2.2.2.2.2.1
    have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
    have hn : 0 < stCap S.mem c.st := by omega
    obtain ⟨-, -, -, h48⟩ := hA.ev.sok.2.2.2.2.1 hn
    simp only [Cx.qv]; omega
  have hqX : c.qv s X.mem = c.qv s S.mem := by rw [hm]
  have t1 := tNat (by omega : c.qv s S.mem < 2 ^ 64); have t2 := tNat (by omega : 3 * c.vl < 2 ^ 64)
  have t3 := tNat (by omega : c.st < 2 ^ 64); have t4 := tNat (by omega : c.t0 < 2 ^ 64)
  have t5 := tNat (by omega : qn < 2 ^ 64); have t6 := tNat (by omega : c.vl / 2 + 1 < 2 ^ 64)
  have t7 := tNat (by omega : c.vp < 2 ^ 64); have t8 := tNat (by omega : c.vl / 2 - 1 < 2 ^ 64)
  have t9 := tNat (by omega : c.vc < 2 ^ 64)
  rw [← hqX] at t1 h0
  refine ReachesRet.call_regions (mulSum impl hap R ns hcode hmul c.Hq bk Lk (X.regs 0) (X.regs 1) (X.regs 2) (X.regs 3)
    (X.regs 4) (X.regs 5) (X.regs 6) (X.regs 7) (X.regs 8) (X.regs 9)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 r4 : BitVec 64).toNat = r4 := by decide
    rw [h30, e30]; exact raS impl hap _ hns _ (by decide) (by decide) (by decide) (by decide +kernel)
  case pre =>
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, t1, t2, t3, t4, t5, t6, t7, t8, t9]
    exact mul_pre hcr (by rw [hm]; exact hA.ev) (by rw [hm]; exact hA.fp) (by rw [hm]; exact hA.rg) hqle hspn h28
      hk ha (by rw [hm]; exact hA.bud)
  simp only [h0, h2, h3, h4, h5, h6, h7, h8, h9, t1, t2, t3, t4, t5, t6, t7, t8, t9] at hq
  obtain ⟨hr0, hr1, hr2, L', b', hmc⟩ := mul_post hA hm hspn h28 hk ha hq hrg
  rw [hqX] at hr0
  exact k T (by rw [hT, h30]) (f1.trans hsp) (f2.trans h28) (f3.trans h29) (f4.trans h18) hr0 hr1 hr2 ⟨L', b', by rw [← hqX]; exact hmc⟩ (by omega)

end FvModexp.Arm64.Q.DivRec
