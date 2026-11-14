import FvModexp.Proofs.Amd64.NatQ.DrsFD6R
import FvModexp.Proofs.Amd64.NatQ.DrsFD6
import FvModexp.Proofs.Amd64.NatQ.DrsFD5R
import FvModexp.Proofs.Amd64.NatQ.DrsFD5
import FvModexp.Proofs.Amd64.NatQ.DrsFD4
import FvModexp.Proofs.Amd64.NatQ.DrsFD3
import FvModexp.Proofs.Amd64.NatQ.DrsFD1
import FvModexp.Proofs.Amd64.NatQ.DrsFD7
import FvModexp.Proofs.Amd64.NatQ.DrsFD2
import FvModexp.Proofs.Amd64.NatQ.DrsFC5R
import FvModexp.Proofs.Amd64.NatQ.DrsDL

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFDL.lean; composition pattern of Amd64/NatQ/DrsDL.lean)
# `divRecursiveStep` (amd64), the end of the final block (natdiv.go:880-892)

`afterF`: `EF` (`0x5f050a`) → `Kept ∧ DrsPostW` (`QF`), composing `d1F` (`u.norm()`), `d2F` (`nat.cmp`), `d3F`/`d4F`
(`u[:ql] -= qhatv`), `d5rF`/`d5F` (the borrow into `u[ql:]`, `borrowF`), `d6rF`/`d6F` (`addTo(z, qhat.norm())`),
`d7F` (deferred `stk.restore`, return).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- from `0x5f0630` (`McF` at `Cx.sGF`) to the return -/
theorem tail6F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rJF6) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : McF R c s Lk bk T.mem j Z U qv (c.sGF s U)) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T (QF R c s) :=
  d6rF impl R c s Lk bk j Z U qv _ T hpc hsp h5 h14 hfs hdf hx15 hmc
    fun X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 hle hv hN =>
      d6F impl hap R hmv c s Lk bk j Z U qv _ T hmc X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
        hle hv hN fun T' hT' L' b' hG => d7F impl R c s L' b' j Z U T' hT' hG

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
theorem afterF (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv : Nat)
    (hE : EF R c s Lk bk S j Z U qv) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S (QF R c s) := by
  have hmcE : McF R c s Lk bk S.mem j Z U qv (c.sFF s U) := hE.mc
  have hcr := hmcE.cr
  have he := e_leF hcr hmcE.li hmcE.jB
  have hwE : Asm.limbs S.mem c.up c.u1 = (c.sFF s U).w := hmcE.wk
  have hbl : (c.sFF s U).buf.length = 3 * c.vl := by rw [← hmcE.bf, Asm.length_limbs]
  have hq3 : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by have := hcr.h40; omega)
  have hbw := borrowF hmcE
  refine d1F impl R c s Lk bk S j Z U qv hE _
    fun X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hle hv hN => ?_
  refine d2F impl hap R c s Lk bk S j Z U qv hE _ X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hle hv hN
    fun T b1 b2 b3 b4 b5 b6 b7 b8 hmc hv4 => ?_
  refine d3F impl R c s Lk bk j Z U qv (c.sFF s U) _ T b1 b2 b3 b4 b5 b6 b8 hmc hv4 he
    fun X2 c1 c2 c3 c4 c5 c6 hF hreg ra ez en ex ey => ?_
  refine d4F impl hap R c s Lk bk j Z U qv (c.sFF s U) _ T hmc hv4 X2 c1 c2 c3 c4 c5 c6 hF hreg ra ez en ex ey
    fun T' e1 e2 e3 e4 e5 e6 e7 hmc' hv4' hcy => ?_
  have hb1 := subVVc_le1 ((c.sFF s U).w.take (c.PF s U).length) ((c.sFF s U).buf.take (c.PF s U).length) 0
    (by omega)
  refine d5rF impl R c s Lk bk j Z U qv (stS (c.PF s U).length (c.sFF s U)) _ _ hb1 T' e1 e2 e3 e4 e5 e6 e7
    hmc' hv4' hcy (fun hb => (hbw hb).1) (fun X3 f1 f2 f3 f4 f5 f6 f7 fm hb0 => ?_)
    (fun Y g1 g2 g3 g4 g5 g6 g7 y0 y3 y1 y7 y6 y8 y9 yF yr yra hb => ?_)
  · have hG : McF R c s Lk bk X3.mem j Z U qv (c.sGF s U) := by
      rw [fm, ← stSF_zero hbl hq3 hb0]; exact hmc'
    exact tail6F impl hap R hmv c s Lk bk j Z U qv X3 f1 f2 f3 f4 f5 f6 f7 hG
  · exact d5F impl hap R hmv c s Lk bk j Z U qv _ T' hmc' hv4' Y g1 g2 g3 g4 g5 g6 g7 y0 y3 y1 y7 y6 y8 y9 yF yr yra
      S.mem hwE hb (hbw hb).2 fun T5 h1 h2 h3 h4 h5 h6 h7 L5 b5 hmc5 _ =>
        tail6F impl hap R hmv c s L5 b5 j Z U qv T5 h1 h2 h3 h4 h5 h6 h7 hmc5

end FvModexp.Amd64.Q.DivRec
