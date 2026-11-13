import FvModexp.Proofs.Amd64.NatQ.DrsD1
import FvModexp.Proofs.Amd64.NatQ.DrsD2
import FvModexp.Proofs.Amd64.NatQ.DrsD3
import FvModexp.Proofs.Amd64.NatQ.DrsD4
import FvModexp.Proofs.Amd64.NatQ.DrsD5
import FvModexp.Proofs.Amd64.NatQ.DrsD6
import FvModexp.Proofs.Amd64.NatQ.DrsD7

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsDL.lean)
# `divRecursiveStep` (amd64), the end of a loop iteration (natdiv.go:843-853), composed

`after`: the correction loop exit `E` (`0x5eff2e`) → `d1` … `d7` → the loop head `H (j - B)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- from the join `0x5f003f` (`Mc … stG`): `addTo(z[j-B:], qhat)`, `stk.restore`, back edge -/
theorem tail6 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rJ6) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : Mc R c s Lk bk T.mem j Z U qv (c.stG s j U))
    (k : ∀ (L' : List (Nat × Nat)) (b' : Nat) (S' : State), H R c s L' b' S' (j - c.vl / 2) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q :=
  d6r impl R c s Lk bk j Z U qv Q T hpc hsp h5 h14 hfs hdf hx15 hmc
    fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 =>
      d6 impl hap R hmv c s Lk bk j Z U qv Q T hmc X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
        fun T' hT' L' b' hG => d7 impl R c s L' b' j Z U Q T' hT' hG (k L' b')

/-- **the end of a loop iteration**: correction loop exit `E` → loop head `H (j - B)` -/
theorem after (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv : Nat)
    (hE : E R c s Lk bk S j Z U qv) (Q : State → Prop)
    (k : ∀ (L' : List (Nat × Nat)) (b' : Nat) (S' : State), H R c s L' b' S' (j - c.vl / 2) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hmcE : Mc R c s Lk bk S.mem j Z U qv (c.stF s j U) := hE.mc
  have hcr := hmcE.cr
  have he := e_le hcr hmcE.li hmcE.jB
  have hwE : Asm.limbs S.mem (c.uuP j) (c.uuL j) = (c.stF s j U).w := hmcE.wk
  have hbl : (c.stF s j U).buf.length = 3 * c.vl := by rw [← hmcE.bf, Asm.length_limbs]
  have hq3 : (c.P s j U).length ≤ 3 * c.vl := P_len_le (by have := hcr.h40; omega)
  refine d1 impl R c s Lk bk S j Z U qv hE Q
    fun X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hle hv hN => ?_
  refine d2 impl hap R c s Lk bk S j Z U qv hE Q X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hle hv hN
    fun T b1 b2 b3 b4 b5 b6 b7 b8 hmc hv4 => ?_
  refine d3 impl R c s Lk bk j Z U qv (c.stF s j U) Q T b1 b2 b3 b4 b5 b6 b8 hmc hv4 he
    fun X2 c1 c2 c3 c4 c5 c6 hF hreg ra ez en ex ey => ?_
  refine d4 impl hap R c s Lk bk j Z U qv (c.stF s j U) Q T hmc hv4 X2 c1 c2 c3 c4 c5 c6 hF hreg ra ez en ex ey
    fun T' e1 e2 e3 e4 e5 e6 e7 hmc' hv4' hcy => ?_
  have hb1 := subVVc_le1 ((c.stF s j U).w.take (c.P s j U).length) ((c.stF s j U).buf.take (c.P s j U).length) 0
    (by omega)
  refine d5r impl R c s Lk bk j Z U qv (stS (c.P s j U).length (c.stF s j U)) Q _ hb1 T' e1 e2 e3 e4 e5 e6 e7
    hmc' hv4' hcy (fun X3 f1 f2 f3 f4 f5 f6 f7 fm hb0 => ?_)
    (fun Y g1 g2 g3 g4 g5 g6 g7 y0 y3 y1 y7 y6 y8 y9 yF yr yra hb => ?_)
  · have hG : Mc R c s Lk bk X3.mem j Z U qv (c.stG s j U) := by
      rw [fm, ← stS_zero hbl hq3 hb0]; exact hmc'
    exact tail6 impl hap R hmv c s Lk bk j Z U qv Q X3 f1 f2 f3 f4 f5 f6 f7 hG k
  · exact d5 impl hap R hmv c s Lk bk j Z U qv Q T' hmc' hv4' Y g1 g2 g3 g4 g5 g6 g7 y0 y3 y1 y7 y6 y8 y9 yF yr yra
      S.mem hwE hb fun T5 h1 h2 h3 h4 h5 h6 h7 L5 b5 hmc5 _ =>
        tail6 impl hap R hmv c s L5 b5 j Z U qv Q T5 h1 h2 h3 h4 h5 h6 h7 hmc5 k

end FvModexp.Amd64.Q.DivRec
