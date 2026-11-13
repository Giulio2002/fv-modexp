import FvModexp.Proofs.Amd64.NatQ.MulKarLt
import FvModexp.Proofs.Amd64.NatQ.MulLoopClrJ
import FvModexp.Proofs.Amd64.NatQ.MulLoopNatC
import FvModexp.Proofs.Amd64.NatQ.MulLoop
import FvModexp.Proofs.Amd64.NatQ.MulLoopExit

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopPath.lean — TIGHT COSTS] `nat.mul` (amd64), `40 ≤ n < m`: the whole path from the join to the return

`mloop`: `karLt` (`karatsuba(stk, z[:2n], x[:n], y)` → `KA`), `lclr` (`clear(z[2n:])`, the defer record → `LP`),
`lnat` (`t := stk.nat(2n)` → `LH … 0`), `lloop` (the chunks) and `lend` (the exit, the deferred `stk.restore`,
the return) ⟹ `Kept` + `MPost`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

set_option maxRecDepth 20000 in
/-- **`40 ≤ n < m`**: from the join to the return, `MPost` -/
theorem mloop (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n0 : Nat) (ihK : ∀ a, IH impl R H n0 (.kar, a)) (ihM : ∀ a, IH impl R H n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (h40 : 40 ≤ yl.toNat) (hyx : yl.toNat < xl.toNat)
    (hμ : μl xl.toNat yl.toNat + 3 ≤ n0)
    (hra0 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hμk : 8 * yl.toNat + 2 < n0 := by
    have hn : ¬ xl.toNat < yl.toNat := by omega
    simp only [μl, Nat.max_eq_left (Nat.le_of_lt hyx), hn, ite_false] at hμ; omega
  refine karLt impl R n0 S hJ ihK hA h40 hyx hμk hx150 hdf0 fun Lk bk S1 hka => ?_
  refine lclr impl hap R hmc S1 hka hx150 hdf0 fun P hlp => ?_
  refine lnat impl hap R hgr hmc hwb hlp hx150 hdf0 fun Lk' bk' tp tl tc S2 hH => ?_
  exact lloop impl hap R hmv n0 ihM hμ hx150 hdf0
    (fun Lk bk k tp tl tc S hH hge => lend impl hra0 Lk bk k tp tl tc S hH hge)
    _ Lk' bk' 0 tp tl tc S2 (Nat.le_refl _) hH

end FvModexp.Amd64.Q.NatMul
