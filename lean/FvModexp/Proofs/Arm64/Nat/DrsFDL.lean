import FvModexp.Proofs.Arm64.Nat.DrsFD1
import FvModexp.Proofs.Arm64.Nat.DrsFD2
import FvModexp.Proofs.Arm64.Nat.DrsFD3
import FvModexp.Proofs.Arm64.Nat.DrsFD4
import FvModexp.Proofs.Arm64.Nat.DrsFD6
import FvModexp.Proofs.Arm64.Nat.DrsFD7
import FvModexp.Proofs.Arm64.Nat.DrsFC5R
import FvModexp.Proofs.Arm64.Nat.DrsC5
import FvModexp.Proofs.Arm64.Nat.DrsC1
import FvModexp.Proofs.Arm64.Nat.DrsC2
import FvModexp.Proofs.Arm64.Nat.DrsC2B
import FvModexp.Proofs.Arm64.Nat.DrsC3
import FvModexp.Proofs.Arm64.Nat.DrsC4
import FvModexp.Proofs.Arm64.Nat.DrsC4R
import FvModexp.Proofs.Arm64.Nat.DrsC5R
import FvModexp.Proofs.Arm64.Nat.DrsC6
import FvModexp.Proofs.Arm64.Nat.DrsD1
import FvModexp.Proofs.Arm64.Nat.DrsD2
import FvModexp.Proofs.Arm64.Nat.DrsD3
import FvModexp.Proofs.Arm64.Nat.DrsD4
import FvModexp.Proofs.Arm64.Nat.DrsD5
import FvModexp.Proofs.Arm64.Nat.DrsD5R
import FvModexp.Proofs.Arm64.Nat.DrsD6
import FvModexp.Proofs.Arm64.Nat.DrsD6R
import FvModexp.Proofs.Arm64.Nat.DrsFC1
import FvModexp.Proofs.Arm64.Nat.DrsFC2
import FvModexp.Proofs.Arm64.Nat.DrsFC2B
import FvModexp.Proofs.Arm64.Nat.DrsFC3
import FvModexp.Proofs.Arm64.Nat.DrsFC4
import FvModexp.Proofs.Arm64.Nat.DrsFC4R
import FvModexp.Proofs.Arm64.Nat.DrsFC6R
import FvModexp.Proofs.Arm64.Nat.DrsFD5
import FvModexp.Proofs.Arm64.Nat.DrsFD5R
import FvModexp.Proofs.Arm64.Nat.DrsFD6R

/-!
# `divRecursiveStep` (arm64): the end of the final block, from the final correction loop's exit to the return

`afterF`: `EF` (`0x1babd0`) → `Kept ∧ DrsPostW` (`QF`), composing `d1F` (`u.norm()`), `d2F` (`nat.cmp`), `d3F` (the
`panic("impossible")` test, excluded by `e_leF`), `d4F` (`subVV`), `d5rF`/`d5F` (the borrow; its two model premises
`|qhatv| < len u` and "no borrow out of `u`" from `c_zeroF` + `sTF_one`), `d6rF`/`d6F` (`addTo(z, qhat.norm())`),
`d7F` (the deferred `stk.restore`, the return).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- from `0x1bac98` (`McF` at `Cx.sGF`) to the return -/
theorem tail6F (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFD5) (hsp : T.sp = s.sp - 400#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : McF R c s Lk bk T.mem j Z U qv (c.sGF s U)) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T (QF R c s) :=
  d6rF impl R c s Lk bk j Z U qv _ T hpc hsp h28 h29 h18 hmc
    fun X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 am hle hv hN =>
      d6F impl hap R hmv c s Lk bk j Z U qv _ X a1 a2 a3 a4 a5 a6 n' a7 a8 a9 a10 a11 a12 (am ▸ hmc) hle
        (am ▸ hv) (am ▸ hN) fun T' hT' L' b' hG => d7F impl R c s L' b' j Z U T' hT' hG

/-- the two model facts of the last borrow: when `u[:ql] -= qhatv` borrows, `ql < len u` and `u[ql:] -= 1` does not -/
theorem borrowF {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} (hmc : McF R c s Lk bk M j Z U qv (c.sFF s U))
    (h1 : (Mdl.subVV ((c.sFF s U).w.take (c.PF s U).length) ((c.sFF s U).buf.take (c.PF s U).length)).2 = 1) :
    (c.PF s U).length < c.u1 ∧ (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).2 = 0 := by
  have hcr := hmc.cr
  have hc := c_zeroF hcr hmc.li hmc.jB
  have hwl : (c.sFF s U).w.length = c.u1 := by rw [← hmc.wk, Asm.length_limbs]
  have hbl : (c.sFF s U).buf.length = 3 * c.vl := by rw [← hmc.bf, Asm.length_limbs]
  have hq3 : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by have := hcr.h40; omega)
  have e := sTF_one hbl hq3 h1
  have h0 : (Mdl.subVW ((c.sFF s U).w.drop (c.PF s U).length) 1).2 = 0 := by rw [e] at hc; exact hc
  refine ⟨?_, h0⟩
  apply Nat.lt_of_not_le
  intro hge
  have hd : (c.sFF s U).w.drop (c.PF s U).length = [] := List.drop_eq_nil_of_le (by omega)
  rw [hd] at h0
  simp [Mdl.subVW] at h0

/-- **the end of the final block**: final correction loop exit `EF` → return with `Kept ∧ DrsPostW` -/
theorem afterF (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv : Nat)
    (hE : EF R c s Lk bk S j Z U qv) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S (QF R c s) := by
  have hmcE : McF R c s Lk bk S.mem j Z U qv (c.sFF s U) := hE.mc
  have hv4E := hE.v3
  have hcr := hmcE.cr
  have he := e_leF hcr hmcE.li hmcE.jB
  have hwE : Asm.limbs S.mem c.up c.u1 = (c.sFF s U).w := hmcE.wk
  have hbl : (c.sFF s U).buf.length = 3 * c.vl := by rw [← hmcE.bf, Asm.length_limbs]
  have hq3 : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by have := hcr.h40; omega)
  have hbw := borrowF hmcE
  refine d1F impl R c s Lk bk S j Z U qv hE _ fun X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 am hle hv hN => ?_
  refine d2F impl hap R c s Lk bk j Z U qv (c.sFF s U) _ X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    (am ▸ hmcE) (am ▸ hv4E) hle (am ▸ hv) (am ▸ hN) fun T b1 b2 b3 b4 b5 b6 hmc hv4 => ?_
  refine d3F impl R c s Lk bk j Z U qv (c.sFF s U) _ T b1 b2 b3 b4 b5 b6 hmc hv4 he
    fun X2 c1 c2 c3 c4 c5 c6 hF hreg ez en ex ey => ?_
  refine d4F impl hap R c s Lk bk j Z U qv (c.sFF s U) _ T hmc hv4 X2 c1 c2 c3 c4 c5 c6 hF hreg ez en ex ey
    fun T' e1 e2 e3 e4 e5 hmc' hv4' hcy => ?_
  have hb1 := subVVc_le1 ((c.sFF s U).w.take (c.PF s U).length) ((c.sFF s U).buf.take (c.PF s U).length) 0
    (by omega)
  refine d5rF impl R c s Lk bk j Z U qv (stS (c.PF s U).length (c.sFF s U)) _ _ hb1 T' e1 e2 e3 e4 e5 hmc' hv4' hcy
    (fun hb => (hbw hb).1) (fun X3 f1 f2 f3 f4 f5 fm hb0 => ?_) (fun Y g1 g2 g3 g4 g5 g6 y0 y1 y2 y3 y4 y5 y6 ym hb => ?_)
  · have hG : McF R c s Lk bk X3.mem j Z U qv (c.sGF s U) := by
      rw [fm, ← stSF_zero hbl hq3 hb0]; exact hmc'
    exact tail6F impl hap R hmv c s Lk bk j Z U qv X3 f1 f2 f3 f4 f5 hG
  · exact d5F impl hap R hmv c s Lk bk j Z U qv _ Y g1 g2 g3 g4 g5 g6 y0 y1 y2 y3 y4 y5 y6 S.mem hwE (ym ▸ hmc')
      (ym ▸ hv4') hb (hbw hb).2 fun T5 h1 h2 h3 h4 h5 L5 b5 hmc5 _ =>
        tail6F impl hap R hmv c s L5 b5 j Z U qv T5 h1 h2 h3 h4 h5 hmc5

end FvModexp.Arm64.DivRec
