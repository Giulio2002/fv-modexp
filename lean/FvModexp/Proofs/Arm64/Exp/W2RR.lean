import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2One

/-!
# window-2 prologue (arm64): `RR` gets exactly `numWords` words (nat.go:1398-1403), from the return of
`stk.nat(2n).div(stk, RR, zz, m)` (`divRet` = fn+0x41c) to `oneJ`

`len(RR) ≥ n` (then `= n`, `RR < m`): `RR` is the remainder. `len(RR) < n`: `zz = zz.make(n)` reuses `zz` (its
capacity is `≥ 2n + 1`, the `makeslice` branches are refuted), `copy(zz, RR)` (memmove), `RR = zz`; the words
`zz[len RR : n]` are still zero from `zz = 2^(128 n)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

/-- return of `nat.div` (RR) -/
abbrev divRet : Nat := 1802956

/-- the frame words `divRet → oneJ` writes (memmove window, spills) -/
@[reducible] def rw4 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 168, sp + 176), (sp + 256, sp + 272), (sp + 304, sp + 312),
    (sp + 400, sp + 408), (sp + 544, sp + 552), (sp + 600, sp + 608)]

/-- the facts at `oneJ` -/
@[reducible] def RRPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M M' : Memory)
    (rrp rrc : Nat) : Prop :=
  MemFrame M M' (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ LiveFrame M M' L [(zzp, zzp + 8 * n)] ∧
  R.inv b L g (view R.rt L M') ∧ M'.regions = M.regions ∧
  M'.readLE (sp + 544) 8 = rrp ∧ M'.readLE (sp + 264) 8 = rrc ∧ M'.readLE (sp + 256) 8 = n ∧
  M'.readLE (sp + 400) 8 = zzp ∧ M'.readLE (sp + 168) 8 = zzc ∧ M'.readLE rrp (8 * n) = M.readLE rp (8 * rl) ∧
  ((rrp = rp ∧ rrc = rc ∧ rl = n) ∨ (rrp = zzp ∧ rrc = zzc ∧ rl < n))


end FvModexp.Arm64.W2Pro
