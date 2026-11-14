import FvModexp.Proofs.Arm64.Nat.DrsC2B
import FvModexp.Proofs.Arm64.Nat.DrsC5
import FvModexp.Proofs.Arm64.Nat.DrsC5S
import FvModexp.Proofs.Arm64.Nat.DrsC6
import FvModexp.Proofs.Arm64.Nat.DrsC6R
import FvModexp.Proofs.Arm64.Nat.DrsC1
import FvModexp.Proofs.Arm64.Nat.DrsC2
import FvModexp.Proofs.Arm64.Nat.DrsC3
import FvModexp.Proofs.Arm64.Nat.DrsC4
import FvModexp.Proofs.Arm64.Nat.DrsC4R
import FvModexp.Proofs.Arm64.Nat.DrsC5R

/-!
# `divRecursiveStep` (arm64): the whole correction loop (natdiv.go:832-843)

`cl`: from the head `C` after `i` corrections to the exit `E` (induction on `2 - i`), composing `c1` (head/`uu.norm()`),
`c2` (`nat.cmp`), `c2b` (break test), `c3` (`qhat--`), `c4r`/`c4` (`subVV`), `c5r`/`c5`/`c5s` (borrow into
`qhatv[s:]`), `c6` (`addTo`), `c6r` (`i++`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- **the correction loop**: head → exit -/
theorem cl (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop) :
    ∀ (n : Nat) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (i : Nat) (st : Mdl.St), 2 - i = n →
      C R c s Lk bk S j Z U qv i st →
      (∀ (Lk' : List (Nat × Nat)) (bk' : Nat) (S' : State), E R c s Lk' bk' S' j Z U qv →
        ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  intro n
  induction n with
  | zero =>
    intro Lk bk S i st hn hC kE
    exact c1 impl R c s Lk bk S j Z U qv i st hC Q (kE Lk bk) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi _ _ _ => by omega)
  | succ n ih =>
    intro Lk bk S i st hn hC kE
    -- the tail of an iteration from the `addTo` call state
    have kA : ∀ (Lk1 : List (Nat × Nat)) (bk1 : Nat) (X : State), X.pc = BitVec.ofNat 64 addToA →
        X.regs 30 = BitVec.ofNat 64 0x1ba6ec →
        X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1)) → X.regs 1 = BitVec.ofNat 64 (c.u1 - j + 1) →
        X.regs 2 = BitVec.ofNat 64 (c.uc - j + 1) → X.regs 3 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
        X.regs 4 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1) → X.regs 5 = BitVec.ofNat 64 (c.vc - c.vl / 2 + 1) →
        Bx R c s Lk1 bk1 X j Z U qv i st (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length st) →
        ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q :=
      fun Lk1 bk1 X hpc h30 h0 h1 h2 h3 h4 h5 hbx =>
        c6 impl hap R hmv c s Lk1 bk1 j Z U qv i st Q X hpc h30 h0 h1 h2 h3 h4 h5 hbx fun T hT L' b' hbx' =>
          c6r impl R c s L' b' j Z U qv i st Q T hT hbx' fun S' hC' =>
            ih L' b' S' (i + 1) _ (by have := hbx'.hi; omega) hC' kE
    refine c1 impl R c s Lk bk S j Z U qv i st hC Q (kE Lk bk)
      (fun X n' hpc hsp h28 h29 h18 h30 h0 h1 h2 h3 h4 hF hreg hsi hi hle hv hN => ?_)
    refine c2 impl hap R c s Lk bk S j Z U qv i st hC Q X n' hpc hsp h28 h29 h18 h30 h0 h1 h2 h3 h4 hF hreg hsi hi hle
      hv hN (fun T hpc hsp h28 h29 h18 h0 hmc hv4 hsi' => ?_)
    refine c2b impl R c s Lk bk j Z U qv i st Q hi hC.inv T hpc hsp h28 h29 h18 h0 hmc hv4 hsi' (kE Lk bk)
      (fun Y hpc h30 h0 h1 h2 h3 h4 h5 h6 hbx => ?_)
    refine c3 impl hap R hmv c s Lk bk j Z U qv i st Q Y hpc h30 h0 h1 h2 h3 h4 h5 h6 hbx
      (fun T1 hpc1 L1 b1 hbx1 => ?_)
    refine c4r impl R c s L1 b1 j Z U qv i st (stQ st) Q T1 hpc1 hbx1
      (fun X2 hpc2 h30 hsp h28 h29 h18 hF hreg ez en ex ey => ?_)
    refine c4 impl hap R c s L1 b1 j Z U qv i st (stQ st) Q T1 hbx1 X2 hpc2 h30 hsp h28 h29 h18 hF hreg ez en ex ey
      (fun T3 hpc3 hbx3 hcy => ?_)
    exact c5r impl R c s L1 b1 j Z U qv i st Q T3 hpc3 hbx3 hcy (kA L1 b1)
      (fun Y4 hpc4 h30 h0 h1 h2 h3 h4 h5 h6 hlt hbx4 =>
        c5 impl hap R hmv c s L1 b1 j Z U qv i st Q Y4 hpc4 h30 h0 h1 h2 h3 h4 h5 h6 hlt hbx4 fun T5 hpc5 L5 b5 hbx5 =>
          c5s impl R c s L5 b5 j Z U qv i st Q T5 hpc5 hbx5 (kA L5 b5))

end FvModexp.Arm64.DivRec
