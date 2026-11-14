import FvModexp.Proofs.Arm64.Nat.DrsD5
import FvModexp.Proofs.Arm64.Nat.DrsD6R
import FvModexp.Proofs.Arm64.Nat.DrsD6
import FvModexp.Proofs.Arm64.Nat.DrsD7
import FvModexp.Proofs.Arm64.Nat.DrsC5
import FvModexp.Proofs.Arm64.Nat.DrsC1
import FvModexp.Proofs.Arm64.Nat.DrsC2
import FvModexp.Proofs.Arm64.Nat.DrsC3
import FvModexp.Proofs.Arm64.Nat.DrsC4
import FvModexp.Proofs.Arm64.Nat.DrsC4R
import FvModexp.Proofs.Arm64.Nat.DrsC5R
import FvModexp.Proofs.Arm64.Nat.DrsC6
import FvModexp.Proofs.Arm64.Nat.DrsD1
import FvModexp.Proofs.Arm64.Nat.DrsD2
import FvModexp.Proofs.Arm64.Nat.DrsD3
import FvModexp.Proofs.Arm64.Nat.DrsD4
import FvModexp.Proofs.Arm64.Nat.DrsD5R

/-!
# `divRecursiveStep` (arm64): the end of a loop iteration, from the correction loop's exit to the loop head

`after`: `E` (`0x1ba80c`) → `H (j - B)` (`0x1ba504`), composing `d1` (`uu.norm()`), `d2` (`nat.cmp`), `d3` (the
`panic("impossible")` test, excluded by `e_le`), `d4` (`subVV`), `d5r`/`d5` (the borrow), `d6r`/`d6` (`addTo(z[j-B:],
qhat)`), `d7` (`j -= B; stk.restore(mark)`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- from `0x1ba8d4` (`Mc` at `Cx.stG`) to the loop head -/
theorem tail6 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rD5) (hsp : T.sp = s.sp - 400#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : Mc R c s Lk bk T.mem j Z U qv (c.stG s j U))
    (k : ∀ (L' : List (Nat × Nat)) (b' : Nat) (S' : State), H R c s L' b' S' (j - c.vl / 2) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q :=
  d6r impl R c s Lk bk j Z U qv Q T hpc hsp h28 h29 h18 hmc fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 am =>
    d6 impl hap R hmv c s Lk bk j Z U qv Q X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 (am ▸ hmc)
      fun T' hT' L' b' hG => d7 impl R c s L' b' j Z U Q T' hT' hG (k L' b')

/-- **the end of a loop iteration**: correction loop exit `E` → loop head `H (j - B)` -/
theorem after (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv : Nat)
    (hE : E R c s Lk bk S j Z U qv) (Q : State → Prop)
    (k : ∀ (L' : List (Nat × Nat)) (b' : Nat) (S' : State), H R c s L' b' S' (j - c.vl / 2) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hmcE : Mc R c s Lk bk S.mem j Z U qv (c.stF s j U) := hE.mc
  have hv4E := hE.v4
  have hcr := hmcE.cr
  have he := e_le hcr hmcE.li hmcE.jB
  have hwE : Asm.limbs S.mem (c.uuP j) (c.uuL j) = (c.stF s j U).w := hmcE.wk
  have hbl : (c.stF s j U).buf.length = 3 * c.vl := by rw [← hmcE.bf, Asm.length_limbs]
  have hq3 : (c.P s j U).length ≤ 3 * c.vl := P_len_le (by have := hcr.h40; omega)
  refine d1 impl R c s Lk bk S j Z U qv hE Q fun X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 am hle hv hN => ?_
  refine d2 impl hap R c s Lk bk j Z U qv (c.stF s j U) Q X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    (am ▸ hmcE) (am ▸ hv4E) hle (am ▸ hv) (am ▸ hN) fun T b1 b2 b3 b4 b5 b6 hmc hv4 => ?_
  refine d3 impl R c s Lk bk j Z U qv (c.stF s j U) Q T b1 b2 b3 b4 b5 b6 hmc hv4 he
    fun X2 c1 c2 c3 c4 c5 c6 hF hreg ez en ex ey => ?_
  refine d4 impl hap R c s Lk bk j Z U qv (c.stF s j U) Q T hmc hv4 X2 c1 c2 c3 c4 c5 c6 hF hreg ez en ex ey
    fun T' e1 e2 e3 e4 e5 hmc' hv4' hcy => ?_
  have hb1 := subVVc_le1 ((c.stF s j U).w.take (c.P s j U).length) ((c.stF s j U).buf.take (c.P s j U).length) 0
    (by omega)
  refine d5r impl R c s Lk bk j Z U qv (stS (c.P s j U).length (c.stF s j U)) Q _ hb1 T' e1 e2 e3 e4 e5 hmc' hv4' hcy
    (fun X3 f1 f2 f3 f4 f5 fm hb0 => ?_) (fun Y g1 g2 g3 g4 g5 g6 y0 y1 y2 y3 y4 y5 y6 ym hb => ?_)
  · have hG : Mc R c s Lk bk X3.mem j Z U qv (c.stG s j U) := by
      rw [fm, ← stS_zero hbl hq3 hb0]; exact hmc'
    exact tail6 impl hap R hmv c s Lk bk j Z U qv Q X3 f1 f2 f3 f4 f5 hG k
  · exact d5 impl hap R hmv c s Lk bk j Z U qv Q Y g1 g2 g3 g4 g5 g6 y0 y1 y2 y3 y4 y5 y6 S.mem hwE (ym ▸ hmc')
      (ym ▸ hv4') hb fun T5 h1 h2 h3 h4 h5 L5 b5 hmc5 _ =>
        tail6 impl hap R hmv c s L5 b5 j Z U qv Q T5 h1 h2 h3 h4 h5 hmc5 k

end FvModexp.Arm64.DivRec
