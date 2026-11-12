import FvModexp.Proofs.Arm64.Nat.LibRem
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.Restore
import FvModexp.Proofs.Arm64.Nat.LibDiv
import FvModexp.Proofs.Arm64.Exp.NHyp
import FvModexp.Proofs.Arm64.Exp.ExpHypL

set_option autoImplicit false

/-!
# `(z nat) rem(stk *stack, u, v nat) (r nat)` (go-bigmodexpfix natdiv.go:505), arm64 — statement and frame

```go
func (z nat) rem(stk *stack, u, v nat) (r nat) {
	if alias(z, u) { z = nil }
	defer stk.restore(stk.save())
	q := stk.nat(max(1, len(u)-(len(v)-1)))
	_, r = q.div(stk, z, u, v)
	return r
}
```
Arguments `X0..X2 = z`, `X3 = stk`, `X4..X6 = u`, `X7..X9 = v`; result `X0..X2 = r`. Frame 208 (`MOVD.W R30, -208(RSP)`,
`SP' = SP - 208`): saved `X30` at `SP - 208`, `X29` at `SP - 216`; spills `SP + 8 … SP + 88` (`above = 88 ≤ 112`);
`z` slots `SP - 48` (ptr), `SP - 88` (len), `SP - 80` (cap); defer bit `SP - 89`; closure `{deferwrap1, stk, len}` at
`SP - 40 … SP - 16`, its pointer at `SP - 16`; result slots `SP - 72 … SP - 48`. `q` has `k = len u - len v + 1`
words (`max(1, ·)` of the signed difference = the `Nat` difference `+ 1`). `div` runs at `SP'` with window
`41504 / 112`, so `rem`'s window is `41712 = 208 + 41504`.

The statement is agent expmc's `NHyp.RemHyp` (`CPre … ∧ 0 < len v` → `CPostR`) with ONE extra pre conjunct `NoAlias`
(`¬alias(z, u)`: cap ends differ; NOTES-conventions "[asm s31] FINDING"): under `CPre` alone `alias(z, u)` is possible
and then `rem` may return `nil`, which `CPostR`'s `NatOF … zp zc` cannot express.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.NatRem

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem"

/-- the deferred closure's code (`ADRP 0(PC); ADD $432` at `fn + 0x90`) -/
abbrev dfnA : Nat := 0x1b91b0

/-- the scratch length `max(1, len u - (len v - 1))` -/
@[reducible] def kq (ul vl : Nat) : Nat := ul - vl + 1

/-- the stack need: `stk.nat(k)` then `div` at length `len + rnd k` (`+ 16·len u + 64`) -/
@[reducible] def need (ul _vl : Nat) : Nat := 17 * ul + 68

/-- the budget: `stk.nat(k)` and one `div` (whose budget function is `cd`) -/
@[reducible] def cost (cd : Nat → Nat → Nat → Nat) (l ul vl : Nat) : Nat :=
  stackNatCost l (kq ul vl) + cd (l + StackNat.rnd (kq ul vl)) ul vl

/-- `¬alias(z, u)` (nat.go `alias`: the addresses of the last cap words differ, as 64-bit machine addresses) -/
@[reducible] def NoAlias (zp zc up uc : Nat) : Prop :=
  0 < zc → 0 < uc → (zp + 8 * (zc - 1)) % 2 ^ 64 ≠ (up + 8 * (uc - 1)) % 2 ^ 64

/-- the precondition (`NHyp.RemHyp`'s + `NoAlias`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (cd : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st up ul uc vp vl : Nat) (s : State) : Prop :=
  (CPre R b L 41712 112 zp zl zc st [(up, ul), (vp, vl)] (need ul vl) (cost cd (stLen s.mem st) ul vl) s ∧
    0 < vl) ∧ NoAlias zp zc up uc

/-- the postcondition (`NHyp.CPostR`, value `U mod V`) -/
@[reducible] def Post (R : RtInv) (b : Nat) (cd : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st up ul vp vl : Nat) (s s' : State) : Prop :=
  CPostR R b L 41712 112 zp zc st (natVal s.mem up ul % natVal s.mem vp vl) (cost cd (stLen s.mem st) ul vl) s s'

/-- `NHyp.RemHyp` with the `NoAlias` pre conjunct (the form asm proves) -/
def RemHypNA (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnRem)
      [z, zl, zc, st, u, ul, uc, v, vl, vc]
      (fun s => (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(u.toNat, ul.toNat), (v.toNat, vl.toNat)]
          (need ul.toNat vl.toNat) (cost (stLen s.mem st.toNat) ul.toNat vl.toNat) s ∧
        0 < vl.toNat) ∧ NoAlias z.toNat zc.toNat u.toNat uc.toNat)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem u.toNat ul.toNat % natVal s.mem v.toNat vl.toNat)
        (cost (stLen s.mem st.toNat) ul.toNat vl.toNat) s s')

/-- the `div` callee's statement used (`ExpHyp.DivHypL` on `nat.div`'s program `LibDiv.names` = `NatDiv.names`) -/
abbrev DHyp (impl : List Segment) (R : RtInv) (cd : Nat → Nat → Nat → Nat) : Prop :=
  ExpHyp.DivHypL impl R LibDiv.names 41504 112 cd

/-- the ranges `rem` writes in its own frame -/
@[reducible] def fw (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 216, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 88)]

/-- the frame slots read after `stk.nat` (memory `M`) -/
structure Sl (s : State) (zp zl zc st up ul uc vp vl vc : Nat) (M : Memory) : Prop where
  lr : M.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 216) 8 = (s.regs 29).toNat
  dbit : M.readLE (s.sp.toNat - 89) 1 = 1
  zl' : M.readLE (s.sp.toNat - 88) 8 = zl
  zc' : M.readLE (s.sp.toNat - 80) 8 = zc
  zp' : M.readLE (s.sp.toNat - 48) 8 = zp
  dfn : M.readLE (s.sp.toNat - 40) 8 = dfnA
  dst : M.readLE (s.sp.toNat - 32) 8 = st
  dn : M.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s3 : M.readLE (s.sp.toNat + 32) 8 = st
  s4 : M.readLE (s.sp.toNat + 40) 8 = up
  s5 : M.readLE (s.sp.toNat + 48) 8 = ul
  s6 : M.readLE (s.sp.toNat + 56) 8 = uc
  s7 : M.readLE (s.sp.toNat + 64) 8 = vp
  s8 : M.readLE (s.sp.toNat + 72) 8 = vl
  s9 : M.readLE (s.sp.toNat + 80) 8 = vc

/-- the slots survive a frame that avoids `[SP - 216, SP - 200) ∪ [SP - 96, SP - 8) ∪ [SP + 8, SP + 88)` -/
theorem Sl.frame {s : State} {zp zl zc st up ul uc vp vl vc : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Sl s zp zl zc st up ul uc vp vl vc M) (hF : MemFrame M M' ws)
    (ho : ∀ a n, (s.sp.toNat - 216 ≤ a ∧ a + n ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 96 ≤ a ∧ a + n ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 88) → Outside a n ws)
    (h0 : 216 ≤ s.sp.toNat) :
    Sl s zp zl zc st up ul uc vp vl vc M' := by
  have r : ∀ a n, (s.sp.toNat - 216 ≤ a ∧ a + n ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 96 ≤ a ∧ a + n ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + n ≤ s.sp.toNat + 88) → M'.readLE a n = M.readLE a n :=
    fun a n hh => hF.readLE a n (ho a n hh)
  exact ⟨(r _ _ (by omega)).trans h.lr, (r _ _ (by omega)).trans h.fp, (r _ _ (by omega)).trans h.dbit,
    (r _ _ (by omega)).trans h.zl', (r _ _ (by omega)).trans h.zc', (r _ _ (by omega)).trans h.zp',
    (r _ _ (by omega)).trans h.dfn, (r _ _ (by omega)).trans h.dst, (r _ _ (by omega)).trans h.dn,
    (r _ _ (by omega)).trans h.dp, (r _ _ (by omega)).trans h.s3, (r _ _ (by omega)).trans h.s4,
    (r _ _ (by omega)).trans h.s5, (r _ _ (by omega)).trans h.s6, (r _ _ (by omega)).trans h.s7,
    (r _ _ (by omega)).trans h.s8, (r _ _ (by omega)).trans h.s9⟩

/-- the call `CALL (*stack).nat` -/
abbrev callNat : Nat := 0x1b9100

/-- the call `CALL nat.div` -/
abbrev callDiv : Nat := 0x1b912c

/-- the facts at `CALL (*stack).nat` (state `P`) -/
structure AtNat (s P : State) (zp zl zc st up ul uc vp vl vc : Nat) : Prop where
  pc : P.pc = BitVec.ofNat 64 callNat
  sp : P.sp = s.sp - 208#64
  r28 : P.regs 28 = s.regs 28
  r29 : P.regs 29 = s.sp - 216#64
  r18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (kq ul vl)
  fr : MemFrame s.mem P.mem (fw s)
  reg : P.mem.regions = s.mem.regions
  sl : Sl s zp zl zc st up ul uc vp vl vc P.mem

end FvModexp.Arm64.NatRem
