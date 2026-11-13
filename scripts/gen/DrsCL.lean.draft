import FvModexp.Proofs.Amd64.NatQ.DrsC1
import FvModexp.Proofs.Amd64.NatQ.DrsC2
import FvModexp.Proofs.Amd64.NatQ.DrsC5
import FvModexp.Proofs.Amd64.NatQ.DrsC5S
import FvModexp.Proofs.Amd64.NatQ.DrsC6
import FvModexp.Proofs.Amd64.NatQ.DrsC6R

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsCL.lean)
# `divRecursiveStep` (amd64): the whole correction loop (natdiv.go:832-843)

`cl`: from the head `C` after `i` corrections to the exit `E` (induction on `2 - i`), composing `c1` (head/`uu.norm()`),
`c2` (`nat.cmp`), `c2b` (break test), `c3` (`qhat--`), `c4r`/`c4` (`subVV.abi0` + re-entry), `c5r`/`c5`/`c5s` (borrow
into `qhatv[s:]`), `c6` (`addTo`), `c6r` (`i++`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

/-- **the correction loop**: head → exit -/
theorem cl (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop) :
    ∀ (n : Nat) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (i : Nat) (st : Mdl.St), 2 - i = n →
      C R c s Lk bk S j Z U qv i st →
      (∀ (Lk' : List (Nat × Nat)) (bk' : Nat) (S' : State), E R c s Lk' bk' S' j Z U qv →
        ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  intro n
  induction n with
  | zero =>
    intro Lk bk S i st hn hC kE
    have := hC.hi
    exact c1 impl R c s Lk bk S j Z U qv i st hC Q (kE Lk bk)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi _ _ _ => by omega)
  | succ n ih =>
    intro Lk bk S i st hn hC kE
    -- the tail of an iteration from the `addTo` call
    have kA : ∀ (Lk1 : List (Nat × Nat)) (bk1 : Nat) (T X : State),
        Bx R c s Lk1 bk1 T j Z U qv i st (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length st) →
        X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 → X.regs 5 = s.regs 4 - 8#64 →
        X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 →
        X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1)) → X.regs 3 = BitVec.ofNat 64 (c.u1 - j + 1) →
        X.regs 1 = BitVec.ofNat 64 (c.uc - (j - 1)) → X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
        X.regs 6 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1) → X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) →
        MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
        X.mem.readLE ((s.regs 4).toNat - 400) 8 = rA →
        ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q :=
      fun Lk1 bk1 T X hby hpc hsp h5 h14 hfs hdf hx15 h0 h3 h1 h7 h6 h8 hFR hreg hra =>
        c6 impl hap R hmv c s Lk1 bk1 j Z U qv i st Q T hby X hpc hsp h5 h14 hfs hdf hx15 h0 h3 h1 h7 h6 h8 hFR hreg hra
          fun T' hT L' b' hbx' =>
            c6r impl R c s L' b' j Z U qv i st Q T' hT hbx' fun S' hC' =>
              ih L' b' S' (i + 1) _ (by have := hbx'.hi; omega) hC' kE
    refine c1 impl R c s Lk bk S j Z U qv i st hC Q (kE Lk bk)
      (fun X n' hpc hsp h5 h14 hfs hdf hx15 h0 h3 h1 h7 h6 hF hreg hra hsi hi hle hv hN => ?_)
    refine c2 impl hap R c s Lk bk S j Z U qv i st hC Q X n' hpc hsp h5 h14 hfs hdf hx15 h0 h3 h1 h7 h6 hF hreg hra hsi
      hi hle hv hN (fun T hpc hsp h5 h14 hfs hdf hx15 h0 hmc hv4 hsi' => ?_)
    refine c2b impl R c s Lk bk j Z U qv i st Q hi hC.inv T hpc hsp h5 h14 hfs hdf hx15 h0 hmc hv4 hsi' (kE Lk bk)
      (fun Y hbx hpc hsp h5 h14 hfs hdf hx15 h0 h3 h1 h7 h6 h8 h9 hFR hreg hra => ?_)
    refine c3 impl hap R hmv c s Lk bk j Z U qv i st Q T hbx Y hpc hsp h5 h14 hfs hdf hx15 h0 h3 h1 h7 h6 h8 h9 hFR
      hreg hra (fun T1 hpc1 L1 b1 hbx1 => ?_)
    refine c4r impl R c s L1 b1 j Z U qv i st (stQ st) Q T1 hpc1 hbx1
      (fun X2 hpc2 hsp2 h52 h142 hfs2 hdf2 hF2 hreg2 hra2 ez en ex ey => ?_)
    refine c4 impl hap R c s L1 b1 j Z U qv i st (stQ st) Q T1 hbx1 X2 hpc2 hsp2 h52 h142 hfs2 hdf2 hF2 hreg2 hra2
      ez en ex ey (fun T3 hpc3 hby3 hcy => ?_)
    exact c5r impl R c s L1 b1 j Z U qv i st Q T3 hpc3 hby3 hcy (kA L1 b1 T3)
      (fun Y4 hby4 hlt hpc4 hsp4 h54 h144 hfs4 hdf4 hx154 h04 h34 h14' h74 h64 h84 h94 hFR4 hreg4 hra4 =>
        c5 impl hap R hmv c s L1 b1 j Z U qv i st Q T3 hby4 hlt Y4 hpc4 hsp4 h54 h144 hfs4 hdf4 hx154 h04 h34 h14' h74
          h64 h84 h94 hFR4 hreg4 hra4 fun T5 hpc5 L5 b5 hbx5 =>
            c5s impl R c s L5 b5 j Z U qv i st Q T5 hpc5 hbx5 (kA L5 b5 T5))

end FvModexp.Amd64.Q.DivRec
