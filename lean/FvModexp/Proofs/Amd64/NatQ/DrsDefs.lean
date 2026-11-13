import FvModexp.Proofs.Amd64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Amd64.NatQ.MulHypQE
import FvModexp.Proofs.Amd64.Nat.LibDrs
import FvModexp.Proofs.Common.MulCost
import FvModexp.Proofs.Common.DivRec

set_option autoImplicit false

/-!
# `(z nat) divRecursiveStep(stk *stack, u, v nat, depth int)` (go-bigmodexpfix natdiv.go:750), amd64, Q-form —
statements of the recursion family (twin of Arm64/Nat/DrsDefs.lean + Arm64/NatQ/DrsDefs.lean; asm s41)

Same model and structure as arm64 (induction on `len v`, `Summary.induction_mutual` over `Args`, program `LibDrs` = the
division tree without `divLarge` / `nat.div`). amd64 (disassembly `cache-asm/dev/nb-divRecursiveStep-amd64.dis`, entry
`0x5ef880`): Go ABIInternal `RAX, RBX, RCX = z (q)`, `RDI = stk`, `RSI, R8, R9 = u`, `R10 = depth`, `v` ON THE STACK at
`RSP + 8 / + 16 / + 24`. Frame `PUSHQ BP; SUBQ $0x180, SP` (`SP' = RSP - 392`, a callee's entry `RSP - 400`, as arm64);
register spills `RSP + 32 … + 88` (`above = 96`).
Locals (offsets from the ENTRY `RSP` = `r`; `SP' + x = r - 392 + x`): saved `RBP` `r - 8`, defer record pointer
`r - 16` (`0x178`), defer record `{deferwrap1, stk, len(stk.w)}` `r - 48, - 40, - 32` (`0x150 …`), defer bit (byte)
`r - 297` (`0x5f`), …(see the segment modules).
* window: the member pre takes `W ≥ drsW64 (len v)`, one level down `W - 400`; the deepest callee is `nat.mul`
  (`mulWX64 = 30792`): `drsW64 n = 31192 + 400·log₂(n - 3) ≤ 40960` for `n ≤ 2^9`.
* budget: the level-free `Q.drsCQ ul vl` (Amd64/NatQ/DivHypQ, = arm64's); the reserve level `Hq` is fixed along the
  recursion (the inner call is made with the caller's `Hq`).
* `nat.mul`: premise `Q.DivRec.MulHypQE impl R ns W` (Amd64/NatQ/MulHypQE).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

def fn : String := DivLarge.drsFn
def names : List String := DivLarge.drsNames

theorem entry_drs : segAddr Extracted.program DivLarge.drsFn = 0x5ef880 := by decide

/-! ## Window -/

/-- the window of `divRecursiveStep` on a divisor of `n` words (amd64: `nat.mul`'s `mulWX64 = 30792` + 400) -/
def drsW64 (n : Nat) : Nat := 31192 + 400 * Nat.log2 (n - 3)

theorem drsW64_ge (n : Nat) : 31192 ≤ drsW64 n := by unfold drsW64; omega

/-- the recursive call runs one frame (400) down on `n - n/2 + 1` words -/
theorem drsW64_inner {n : Nat} (h : 40 ≤ n) : drsW64 (n - n / 2 + 1) + 400 ≤ drsW64 n := by
  unfold drsW64
  have := log2_step (a := n - n / 2 + 1 - 3) (b := n - 3) (by omega) (by omega)
  omega

theorem drsW64_le {n : Nat} (h : n ≤ 2 ^ 9) : drsW64 n ≤ 40960 := by
  unfold drsW64
  have h1 : Nat.log2 (n - 3) ≤ Nat.log2 (2 ^ 9) := log2_mono (by omega)
  have h2 : Nat.log2 (2 ^ 9) = 9 := by decide
  omega

/-! ## The recursion as one family of summaries -/

/-- a call: reserve level, budget, live set, window, the eight register arguments `z = (qp, ql, qc)`, `stk`,
`u = (up, ul, uc)`, `depth`, and the stack arguments `v = (vp, vl, vc)` -/
structure Args where
  Hq : Nat
  b : Nat
  L : List (Nat × Nat)
  W : Nat
  qp : BitVec 64
  ql : BitVec 64
  qc : BitVec 64
  st : BitVec 64
  up : BitVec 64
  ul : BitVec 64
  uc : BitVec 64
  d : BitVec 64
  vp : Nat
  vl : Nat
  vc : Nat

/-- the register arguments and the return-address / `X15` / `DF` facts at the entry -/
@[reducible] def Entry (a : Args) (s : State) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
    s.regs 0 = a.qp ∧ s.regs 3 = a.ql ∧ s.regs 1 = a.qc ∧ s.regs 7 = a.st ∧ s.regs 6 = a.up ∧ s.regs 8 = a.ul ∧
    s.regs 9 = a.uc ∧ s.regs 10 = a.d

/-- the member precondition: window large enough, `DrsPreW` (Q-form, level `a.Hq`) with the budget `drsCQ` -/
def preOf (R : RtInv) (a : Args) (s : State) : Prop :=
  Entry a s ∧ drsW64 a.vl ≤ a.W ∧
    DrsPreW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl) a.W a.qp.toNat a.ql.toNat a.qc.toNat
      a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat a.vp a.vl a.vc s

/-- the callee-saved part of the post -/
@[reducible] def Kept (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

def postOf (R : RtInv) (a : Args) (s s' : State) : Prop :=
  Kept s s' ∧ DrsPostW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl) a.W a.qp.toNat a.ql.toNat
    a.st.toNat a.up.toNat a.ul.toNat a.vp a.vl s s'

/-- the measure: the divisor length -/
def μ (a : Args) (_ : State) : Nat := a.vl

/-- the program of the summary -/
abbrev P (impl : List Amd64.Segment) : Amd64.Program := LibDrs.program.link impl

/-- the induction hypothesis below measure `n` -/
@[reducible] def IH (impl : List Amd64.Segment) (R : RtInv) (n : Nat) (a : Args) : Prop :=
  Summary (P impl) 0x5ef880 (fun s => preOf R a s ∧ μ a s < n) (postOf R a)

end FvModexp.Amd64.Q.DivRec
