import FvModexp.Proofs.Arm64.Nat.DrsFC2B
import FvModexp.Proofs.Arm64.Nat.DrsFC5S
import FvModexp.Proofs.Arm64.Nat.DrsFC6X
import FvModexp.Proofs.Arm64.Nat.DrsC1
import FvModexp.Proofs.Arm64.Nat.DrsC2
import FvModexp.Proofs.Arm64.Nat.DrsC2B
import FvModexp.Proofs.Arm64.Nat.DrsC3
import FvModexp.Proofs.Arm64.Nat.DrsC4
import FvModexp.Proofs.Arm64.Nat.DrsC4R
import FvModexp.Proofs.Arm64.Nat.DrsC5
import FvModexp.Proofs.Arm64.Nat.DrsC5R
import FvModexp.Proofs.Arm64.Nat.DrsC6
import FvModexp.Proofs.Arm64.Nat.DrsFC1
import FvModexp.Proofs.Arm64.Nat.DrsFC2
import FvModexp.Proofs.Arm64.Nat.DrsFC3
import FvModexp.Proofs.Arm64.Nat.DrsFC4
import FvModexp.Proofs.Arm64.Nat.DrsFC4R
import FvModexp.Proofs.Arm64.Nat.DrsFC5
import FvModexp.Proofs.Arm64.Nat.DrsFC5R
import FvModexp.Proofs.Arm64.Nat.DrsFC6
import FvModexp.Proofs.Arm64.Nat.DrsFC6R

/-!
# `divRecursiveStep` (arm64): the whole final correction loop (natdiv.go:869-878)

`clF`: from the head `CF` after `i` rounds to the exit `EF` (induction on `2 - i`), composing `c1F` (head/`u.norm()`),
`c2F` (`nat.cmp`), `c2bF` (the `e > 0` test; `e ≤ 0` → `c6rF`), `c3F` (`qhat--`), `c4rF`/`c4F` (`subVV`),
`c5rF`/`c5F`/`c5sF` (borrow into `qhatv[s:]`), `c6F` (`addTo`), `c6xF` (`i++`). Adapted from DrsCL.
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- **the correction loop**: head → exit -/
theorem clF (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop) :
    ∀ (n : Nat) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (i : Nat) (st : Mdl.St), 2 - i = n →
      CF R c s Lk bk S j Z U qv i st →
      (∀ (Lk' : List (Nat × Nat)) (bk' : Nat) (S' : State), EF R c s Lk' bk' S' j Z U qv →
        ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  intro n
  induction n with
  | zero =>
    intro Lk bk S i st hn hC kE
    exact c1F impl R c s Lk bk S j Z U qv i st hC Q (kE Lk bk) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi _ _ _ => by omega)
  | succ n ih =>
    intro Lk bk S i st hn hC kE
    -- the tail of an iteration from the `addTo` call state
    have kA : ∀ (Lk1 : List (Nat × Nat)) (bk1 : Nat) (X : State), X.pc = BitVec.ofNat 64 rFA →
        BxF R c s Lk1 bk1 X j Z U qv i st (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length st) →
        ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q :=
      fun Lk1 bk1 X0 hpc0 hbx0 =>
        c5sF impl R c s Lk1 bk1 j Z U qv i st Q X0 hpc0 hbx0 fun X hpc h30 h0 h1 h2 h3 h4 h5 hbx =>
        c6F impl hap R hmv c s Lk1 bk1 j Z U qv i st Q X hpc h30 h0 h1 h2 h3 h4 h5 hbx fun T hT L' b' hbx' =>
          c6xF impl R c s L' b' j Z U qv i st Q T hT hbx' fun S' hC' =>
            ih L' b' S' (i + 1) _ (by have := hbx'.hi; omega) hC' kE
    refine c1F impl R c s Lk bk S j Z U qv i st hC Q (kE Lk bk)
      (fun X n' hpc hsp h28 h29 h18 h30 h0 h1 h2 h3 h4 hF hreg hsi hi hle hv hN => ?_)
    refine c2F impl hap R c s Lk bk S j Z U qv i st hC Q X n' hpc hsp h28 h29 h18 h30 h0 h1 h2 h3 h4 hF hreg hsi hi hle
      hv hN (fun T hpc hsp h28 h29 h18 h0 hmc hv4 hsi' => ?_)
    refine c2bF impl R c s Lk bk j Z U qv i st Q hi hC.inv T hpc hsp h28 h29 h18 h0 hmc hv4 hsi'
      (fun S' hC' => ih Lk bk S' (i + 1) st (by omega) hC' kE)
      (fun Y hpc h30 h0 h1 h2 h3 h4 h5 h6 hbx => ?_)
    refine c3F impl hap R hmv c s Lk bk j Z U qv i st Q Y hpc h30 h0 h1 h2 h3 h4 h5 h6 hbx
      (fun T1 hpc1 L1 b1 hbx1 => ?_)
    refine c4rF impl R c s L1 b1 j Z U qv i st (stQ st) Q T1 hpc1 hbx1
      (fun X2 hpc2 h30 hsp h28 h29 h18 hF hreg ez en ex ey => ?_)
    refine c4F impl hap R c s L1 b1 j Z U qv i st (stQ st) Q T1 hbx1 X2 hpc2 h30 hsp h28 h29 h18 hF hreg ez en ex ey
      (fun T3 hpc3 hbx3 hcy => ?_)
    exact c5rF impl R c s L1 b1 j Z U qv i st Q T3 hpc3 hbx3 hcy (kA L1 b1)
      (fun Y4 hpc4 h30 h0 h1 h2 h3 h4 h5 h6 hlt hbx4 =>
        c5F impl hap R hmv c s L1 b1 j Z U qv i st Q Y4 hpc4 h30 h0 h1 h2 h3 h4 h5 h6 hlt hbx4 fun T5 hpc5 L5 b5 hbx5 =>
          kA L5 b5 T5 hpc5 hbx5)

end FvModexp.Arm64.DivRec
