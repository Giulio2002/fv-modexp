import FvModexp.Proofs.Amd64.Exp.ExpHyp
import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Amd64.Nat.StackNatCall
import FvModexp.Proofs.Common.StackPot
import FvModexp.Proofs.Common.MulCostQ

set_option autoImplicit false

/-!
# Q-form (TIGHT COSTS) export statements of the division chain (amd64; owner asm) — twin of Arm64/NatQ/DivHypQ.lean

The amortised-stack twins (Common/StackPot) of the amd64 `nat.div` / `nat.rem` premises, in the amd64 vocabulary
(`g = R14`, posts start with `s'.fsBase = s.fsBase ∧ s'.df = s.df`, the TLS slot `FS:-8` apart from what the callee
writes, `u`/`v` of `nat.div` and `v` of `nat.rem` passed on the stack):
* `ExpHyp.DivHypL` → `ExpHyp.DivHypLQ` (`nat.div`, stack given): the pre's cost slot is the pair
  `(stLen + 16·len u + 64 ≤ H ∧ c ≤ b)` with `c = C ul vl + stkR H s.mem st`, the post's `RtPost … c` is
  `RtPostQ … c (stkR H s'.mem st)`;
* `NHyp.RemHypQ` (`nat.rem`, stack given): amd64 twin of arm64 `NHyp.RemHypQ` (`CPre` → amd64 `RemPreQ`).
Level-free costs: copies of the ISA-independent arm64 definitions (`Q.drsCQ`, `Q.DivLarge.costQ`, `Q.NatDiv.costQ`;
same text, natdiv.go:590/520/750) so that amd64 modules need not import arm64 ones.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.Q

/-- **the level-free budget of `divRecursiveStep`** (copy of arm64 `Q.drsCQ`) -/
def drsCQ (ul n : Nat) : Nat :=
  if h : n < 40 then 0 else
    ((ul - n) / (n / 2) + 1) * (drsCQ ul (n - n / 2 + 1) + mulCQ (n / 2 + 1) (n / 2 - 1))
termination_by n
decreasing_by omega

theorem drsCQ_small {ul n : Nat} (h : n < 40) : drsCQ ul n = 0 := by
  rw [drsCQ, dif_pos h]

theorem drsCQ_big {ul n : Nat} (h : ¬ n < 40) : drsCQ ul n =
    ((ul - n) / (n / 2) + 1) * (drsCQ ul (n - n / 2 + 1) + mulCQ (n / 2 + 1) (n / 2 - 1)) := by
  rw [drsCQ, dif_neg h]

/-- the level-free budget of `divLarge` (`il = len uIn`, `vl = len vIn`; `dc` the division's) -/
@[reducible] def DivLarge.costQ (dc : Nat → Nat → Nat) (il vl : Nat) : Nat :=
  makeCost (il + 1) + makeCost (il - vl + 1) + dc (il + 1) vl

/-- the level-free budget of `nat.div` with a given stack -/
@[reducible] def NatDiv.costQ (dc : Nat → Nat → Nat) (ul vl : Nat) : Nat :=
  makeCost ul + makeCost 1 + DivLarge.costQ dc ul vl

end FvModexp.Amd64.Q

namespace FvModexp.Amd64

/-- the Q-form runtime post (amd64 twin of arm64 `RtPostQ`: `g = R14`) -/
@[reducible] def RtPostQ (R : RtInv) (b cost r' : Nat) (L L' : List (Nat × Nat)) (b' : Nat) (s s' : State) : Prop :=
  LiveExt R L L' ∧ b - cost + r' ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem)

end FvModexp.Amd64

namespace FvModexp.Amd64.ExpHyp

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn WrOut)

/-- `DivPre` in the Q-form: the cost slot is `(stLen + 16·len u + 64 ≤ H ∧ c ≤ b)` -/
@[reducible] def DivPreQ (R : RtInv) (b H c : Nat) (L : List (Nat × Nat))
    (stk above zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = u ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc ∧ s.mem.readLE ((s.regs 4).toNat + 32) 8 = v ∧
    s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl ∧ s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc ∧
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧ z2l ≤ z2c ∧
    WrOut R L s stk above zp zc ∧ WrOut R L s stk above z2 z2c ∧
    RdIn R L s stk above u ul ∧ RdIn R L s stk above v vl ∧ ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧
    NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16 ∧ (stCap s.mem st = 0 → stW s.mem st = 0) ∧
    Apart u (8 * ul) st 24 ∧ Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    Apart v (8 * vl) st 24 ∧ Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    st ≠ 0 ∧
    (Apart st 24 ((s.regs 14).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (Apart st 24 (s.fsBase.toNat - 8) 8 ∧
      Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8) ∧
    (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 ∧
    (0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)) ∧
    (∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      Apart p (8 * c) u (8 * ul) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (stLen s.mem st + 16 * ul + 64 ≤ H ∧ c ≤ b) ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧ (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (s.fsBase.toNat - 8) 8) ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- `DivPostL` in the Q-form (`c` the interface cost, `r'` the reserve after the call) -/
@[reducible] def DivPostLQ (R : RtInv) (b c r' : Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPostQ R b c r' L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st)

/-- **`nat.div`, Q-form** (amd64 twin of arm64 `ExpHyp.DivHypLQ`; `cost` level-free, e.g. `Q.NatDiv.costQ Q.drsCQ`) -/
def DivHypLQ (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (cost : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c]
      (fun s => DivPreQ R b H (cost ul vl + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat
        z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
      (fun s s' => DivPostLQ R b (cost ul vl + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s')

end FvModexp.Amd64.ExpHyp

namespace FvModexp.Amd64.NHyp

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn WrOut)
open FvModexp.Amd64.ExpHyp (NatOF StackOK' stWs)

def fnRem : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem"

/-- the free part of the stack `(start, bytes)` -/
@[reducible] def freeOf (m : Memory) (st : Nat) : Nat × Nat :=
  (stW m st + 8 * stLen m st, 8 * (stCap m st - stLen m st))

/-- `¬alias(z, u)` (nat.go `alias`: the addresses of the last cap words differ, as 64-bit machine addresses) -/
@[reducible] def NoAlias (zp zc up uc : Nat) : Prop :=
  0 < zc → 0 < uc → (zp + 8 * (zc - 1)) % 2 ^ 64 ≠ (up + 8 * (uc - 1)) % 2 ^ 64

/-- **`z.rem(stk, u, v)`'s precondition, Q-form** (amd64 twin of arm64 `NHyp.RemHypQ`'s pre = `CPre … ∧ 0 < len v`
+ `NoAlias` + `0 < st` + the level twin): `z` RAX,RBX,RCX, `stk` RDI, `u` RSI,R8,R9 in registers, `v` on the stack at
`RSP+8 … RSP+24`; the TLS slot `FS:-8` apart from the stack header and its free part (`z`'s: `WrOut`) -/
@[reducible] def RemPreQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st up ul uc vp vl vc : Nat)
    (need cst : Nat) (s : State) : Prop :=
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = vl ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = vc) ∧
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ RoOut R ∧
    Outside StackNat.wT 16 R.rt ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧
    (∀ p n, (p, n) ∈ [(up, ul), (vp, vl)] → RdIn R L s stk above p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s.mem p n ∧
      Apart p (8 * n) st 24 ∧ Apart p (8 * n) (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
      (0 < zc → Apart zp (8 * zc) p (8 * n))) ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧ Apart st 24 ((s.regs 14).toNat + 16) 8 ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    (stCap s.mem st = 0 → stW s.mem st = 0) ∧ stLen s.mem st + need ≤ 2 ^ 16 ∧
    s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
    Apart st 24 (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
    (Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (freeOf s.mem st).1 (freeOf s.mem st).2 (s.fsBase.toNat - 8) 8) ∧
    (0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
      Apart zp (8 * zc) RunIface.gA 32) ∧
    Apart st 24 RunIface.gA 32 ∧ Apart (freeOf s.mem st).1 (freeOf s.mem st).2 RunIface.gA 32 ∧
    cst ≤ b ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧ (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (s.fsBase.toNat - 8) 8) ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  0 < vl ∧ NoAlias zp zc up uc ∧ 0 < st ∧ stLen s.mem st + need ≤ H

/-- `CPostR` in the Q-form (amd64: result `RAX,RBX,RCX`; `c` the interface cost, `r'` the reserve after the call) -/
@[reducible] def CPostRQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v c r' : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p l cp : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 cp ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF R L L' s'.mem zp zc 1 p l cp v ∧ RtPostQ R b c r' L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p cp

/-- **`nat.rem`, Q-form** (amd64 twin of arm64 `NHyp.RemHypQ`; `cost` level-free, e.g. `Q.NatDiv.costQ Q.drsCQ`) -/
def RemHypQ (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc : BitVec 64) (v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnRem)
      [z, zl, zc, st, u, ul, uc]
      (fun s => RemPreQ R b H L stk above z.toNat zl.toNat zc.toNat st.toNat u.toNat ul.toNat uc.toNat v vl vc
        (need ul.toNat vl) (cost ul.toNat vl + stkR H s.mem st.toNat) s)
      (fun s s' => CPostRQ R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem u.toNat ul.toNat % natVal s.mem v vl)
        (cost ul.toNat vl + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) s s')

end FvModexp.Amd64.NHyp
