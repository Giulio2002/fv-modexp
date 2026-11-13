import FvModexp.Proofs.Amd64.Nat.DivLargeQR
import FvModexp.Proofs.Amd64.Nat.DivLargeQA1
import FvModexp.Proofs.Amd64.Nat.DivLargeQAm

set_option autoImplicit false

/-!
# `divLarge` (amd64): `alias(z, u)` and `q = z.make(m + 1)` (natdiv.go:620-623), from the alias test to `joinQ`
(`qR`: reuse `z`; `qA1` / `qAm`: `makeslice` with `m = 0` / `m ≠ 0`). Port of `Arm64/Nat/DivLargeQ.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivLarge

theorem qSeg (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDivL.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S)
    (hb : makeCost (il - vl + 1) ≤ bk) (Q : State → Prop)
    (k : ∀ T Lq bq qp qc, AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  by_cases hz : il - vl + 1 ≤ zc
  · exact qR impl R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh hE S hS hz Q
      (fun T h => k T Lk bk zp zc h)
  · by_cases hm0 : il - vl = 0
    · exact qA1 impl R hmk b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh hE S hS (by omega) hm0 hb Q k
    · exact qAm impl R hmk b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh hE S hS (by omega) hm0 hb Q k

end FvModexp.Amd64.DivLarge
