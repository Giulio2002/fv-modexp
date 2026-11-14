import FvModexp.Proofs.Amd64.Exp.W4ZmDefs
import FvModexp.Proofs.Amd64.Exp.W4PowDefs
import FvModexp.Proofs.Amd64.Exp.CmpW
import FvModexp.Proofs.Amd64.Exp.DeferX
import FvModexp.Proofs.Amd64.Nat.NatSub
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Amd64.Nat.Callees2
import FvModexp.Proofs.Common.ExpNorm
import FvModexp.Proofs.Common.ExpFinal
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# window-2 (amd64): the definitions shared by the cut segments (divmc s79 import-chain cut)

Definitions hoisted VERBATIM (same namespaces, same names) out of the segment proof modules (W4ExA/ExB/ExT/Fin/Tail/
ZcP/Mid/Pre4/Mid2/P01Ret/OneDefs/One/Snc/RR/ORet/ORDefs), so that the prologue (`entry → divRet`), the `divRet → RET`
section and the loop/table segments import only definitions and compile independently (twin of the arm64 s67 cut,
`Arm64.W4Posts`/`W4FinDefs`). No statement changes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Loop


/-- `one` (nat.go:1408): a held input apart from the frame, or the frame buffer `sp + 0x148` (`n ≤ 4`) -/
@[reducible] def OneIn (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  Inp R L sp n M0 p ∨ (p = sp + 0x148 ∧ n ≤ 4)

theorem OneIn.c {R : RtInv} {L : List (Nat × Nat)} {g fs sp n p : Nat} {M0 : Memory} (he : Env R L g fs sp M0)
    (h : OneIn R L sp n M0 p) : InpC R L sp n M0 p := by
  rcases h with h | ⟨rfl, hn⟩
  · exact h.c
  · have hs1 : 4296 ≤ sp := he.2.1; have hs2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
    exact ⟨M0.accessible_sub he.2.2.2.1 (Or.inr rfl) (by omega) (by omega), by omega,
      Or.inr (he.2.2.2.2.2.2.2.1.of_sub (by omega) (by omega)), by unfold Apart; omega⟩

end FvModexp.Amd64.W4Loop

namespace FvModexp.Amd64.W4Loop


abbrev njoin : Nat := fnE + 0x11f3

end FvModexp.Amd64.W4Loop

namespace FvModexp.Amd64.W4Loop


/-- the written ranges from the first `zz.cmp(m)` to the join: callee windows, spills, `zz`'s array -/
@[reducible] def jw (R : RtInv) (sp zzp zzc : Nat) : List (Nat × Nat) :=
  R.rt ++ [(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x188, sp + 0x190)] ++ [(zzp, zzp + 8 * zzc)]

/-- what holds at the join point `njoin` (memory `M'`, result `(p, l, c)` in `DI, SI, R8`) relative to the memory `M`
before the final reduction -/
@[reducible] def JoinPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n zzp zzc V : Nat) (M : Memory)
    (p l c : Nat) (M' : Memory) : Prop :=
  ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost n ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧
    M'.regions = M.regions ∧ MemFrame M M' (jw R sp zzp zzc) ∧ LiveFrame M M' L [(zzp, zzp + 8 * zzc)] ∧
    natVal M' p l = V ∧ l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧ NatLive M' R L' p c ∧
    ((p = zzp ∧ c = zzc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
    (l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M'.accessible p (8 * l) false = true))

end FvModexp.Amd64.W4Loop

namespace FvModexp.Amd64.W4Loop


/-- after the norm loop: `CMPQ SI, R8` -/
abbrev tailPc : Nat := fnE + 0x1205

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1"

theorem dE_eq : segAddr LibW.program fnD = 6210496 := by decide

/-- the static facts of the end (memory `M` at the join point; `bp` the caller's frame pointer, `r` the return
address) -/
@[reducible] def FinEnv (sp st n0 bp r : Nat) (M : Memory) : Prop :=
  sp % 8 = 0 ∧ 4296 ≤ sp ∧ sp + 0x3c0 ≤ 2 ^ 48 ∧ M.accessible (sp - 4296) (4296 + 0x3c0) true = true ∧
    M.readLE (sp + 0x378) 8 = sp + 0x340 ∧ M.readLE (sp + 0x340) 8 = 6210496 ∧
    M.readLE (sp + 0x348) 8 = st ∧ M.readLE (sp + 0x350) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 4296) (4296 + 0x3c0) ∧ M.readLE (sp + 0x380) 8 = bp ∧ M.readLE (sp + 0x388) 8 = r ∧ r < 2 ^ 47

/-- what the end guarantees (memory relative to the memory `M` at the join point) -/
@[reducible] def FinPost (sp g fs st n0 bp p l c : Nat) (M : Memory) (s' : State) : Prop :=
  s'.regs 4 = BitVec.ofNat 64 (sp + 0x390) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = BitVec.ofNat 64 g ∧
    s'.fsBase.toNat = fs ∧ s'.xmm 15 = 0 ∧ s'.df = false ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧
    MemFrame M s'.mem [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188), (st + 8, st + 16)]

/-- the stack ranges written by the end before the defer call -/
@[reducible] def ftw (sp : Nat) : List (Nat × Nat) := [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188)]

end FvModexp.Amd64.W4Loop

namespace FvModexp.Amd64.W4Loop


/-- what the return state satisfies, from the loop exit (memory `M`) -/
@[reducible] def TailPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp k0 st n0 bp zp zc zzp zzc : Nat)
    (M0 M : Memory) (s' : State) : Prop :=
  ∃ (M' Mj : Memory) (p l c : Nat), Mem R b L g sp M0 M' zp zc zzp zzc ∧
    M'.readLE zzp (8 * n) = Exp.montgomery n (M.readLE zp (8 * n)) 1 (M0.readLE mp (8 * n)) k0 ∧
    JoinPost R b L g sp n zzp zzc
      (if M0.readLE mp (8 * n) ≤ M'.readLE zzp (8 * n) then 0 else M'.readLE zzp (8 * n)) M' p l c Mj ∧
    FinPost sp g fs st n0 bp p (Expmc.normL Mj p l) c Mj s'

end FvModexp.Amd64.W4Loop

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf)

/-- the spill chain at the first-window `memmove` -/
@[reducible] def zcW (M : Memory) (sp zzc zzp yi k : Nat) : Memory :=
  (((((M.writeLE (sp + 288) 8 zzc).writeLE (sp + 880) 8 zzp).writeLE (sp + 280) 8 yi).writeLE (sp + 320) 8 (k + 1)).writeLE
    (sp + 312) 8 (k * 4)).writeLE (sp - 8) 8 6208751

/-- the slot reads after the copy -/
@[reducible] def ZcSl (m : Memory) (sp n mp mc k0 yp ylen zp zc zzp zzc yi k : Nat) : Prop :=
  m.readLE (sp + 0x168) 8 = zp ∧ m.readLE (sp + 0x138) 8 = k * 4 ∧ m.readLE (sp + 0x88) 8 = zc ∧
  m.readLE (sp + 0x390) 8 = yp ∧ m.readLE (sp + 0x370) 8 = zzp ∧ m.readLE (sp + 0x118) 8 = yi ∧
  m.readLE (sp + 0x120) 8 = zzc ∧ m.readLE (sp + 0x398) 8 = ylen ∧ m.readLE (sp + 0x140) 8 = k + 1 ∧
  m.readLE (sp + 0x3a8) 8 = mp ∧ m.readLE (sp + 0xd8) 8 = k0 ∧ m.readLE (sp + 0x3b0) 8 = n ∧
  m.readLE (sp + 0x3b8) 8 = mc

end FvModexp.Amd64.W4Pro
