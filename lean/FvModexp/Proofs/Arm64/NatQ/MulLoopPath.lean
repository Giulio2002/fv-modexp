import FvModexp.Proofs.Arm64.NatQ.MulKarLt
import FvModexp.Proofs.Arm64.NatQ.MulLoopClrJ
import FvModexp.Proofs.Arm64.NatQ.MulLoopNatC
import FvModexp.Proofs.Arm64.NatQ.MulLoop
import FvModexp.Proofs.Arm64.NatQ.MulLoopExit

/-!
# [Q-form copy of Arm64/Nat/MulLoopPath.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), `40 ≤ n < m` (natmul.go:50-62): the whole path from the join

`karLt`: the join → `karatsuba` (`karLt2` → `KA`); **`mloop`**: `karLt` → `lclr` (`clear(z[2n:])`, defer) → `lnat`
(`t := stk.nat(2n)`) → `lloop` (chunks) with the exit `lend` ⟹ `Kept ∧ MPost`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `40 ≤ n < m`: the join → the call of `karatsuba` (`karLt2`) -/
theorem karLt (impl : List Segment) (R : RtInv) (n0 : Nat) (ih : ∀ a, IH impl R H n0 (.kar, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (h40 : 40 ≤ yl.toNat) (hyx : yl.toNat < xl.toNat)
    (hμ : 8 * yl.toNat + 2 < n0) {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (Lk : List (Nat × Nat)) (bk : Nat) (S' : State),
      KA R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem Lk bk S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  obtain ⟨h40', hthacc⟩ := hJ.thr
  obtain ⟨hpc, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, hsp, h28, h29, h18, mlr, mfp, m120, m296, m304, m312, m320, m328, m336, hreg,
    hpx, hpy, hnx, hny⟩ := hA
  have hst0 : st ≠ 0#64 := by
    obtain ⟨-, -, -, -, -, -, ⟨h, -⟩, -⟩ := hJ.pre
    intro e; apply h; rw [e]; rfl
  have hst0' : (st = 0#64) = False := by simp only [eq_iff_iff, iff_false]; exact hst0
  have hpre := hJ.pre
  obtain ⟨⟨-, ⟨hal0, hb0, ha0, hw0⟩, -⟩, hmw, -, -, -, ⟨-, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hpre
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hsacc : S.mem.accessible (s.sp.toNat - 264) 264 true = true := by
    rw [hJ.F.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hcap := hJ.cap; have hc40 := hJ.c40
  have hp64 : p < 2 ^ 64 := by obtain ⟨-, -, -, h48⟩ := hJ.live (by omega); omega
  janus_run [h40', hst0', toInt_small yl (by omega), toInt_small (BitVec.ofNat 64 40) (by decide)] until [0x1bb038]
  refine karLt2 impl R n0 ih hJ hpx hpy hnx hny h40 hyx hμ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [winA]; janus_frame) ?qreg ?q144 ?q120 ?q96 ?q94 ?q304 ?q328 ?q136 ?q184 ?q296 ?q312 ?q320 ?q336
    ?qlr ?qfp hK
  case qreg => janus_simp; exact hreg
  case q120 => janus_simp; exact m120
  case q304 => janus_simp; exact m304
  case q328 => janus_simp; exact m328
  case q296 => janus_simp; exact m296
  case q312 => janus_simp; exact m312
  case q320 => janus_simp; exact m320
  case q336 => janus_simp; exact m336
  case q136 => janus_simp; omega
  case q184 => janus_simp
  case qlr => janus_simp; exact mlr
  case qfp => janus_simp; exact mfp
  all_goals try janus_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
/-- **`40 ≤ n < m`**: from the join to the return, `MPost` -/
theorem mloop (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n0 : Nat) (ihK : ∀ a, IH impl R H n0 (.kar, a)) (ihM : ∀ a, IH impl R H n0 (.mul, a))
    {b : Nat} {L : List (Nat × Nat)} {W zp zc : Nat} {st xp xl xc yp yl yc : BitVec 64} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} (S : State)
    (hJ : Core R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem)
    (hA : JoinAt s S p c st xp xl xc yp yl yc) (h40 : 40 ≤ yl.toNat) (hyx : yl.toNat < xl.toNat)
    (hμ : μl xl.toNat yl.toNat + 3 ≤ n0) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp zc st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hμk : 8 * yl.toNat + 2 < n0 := by
    simp only [μl, Nat.max_eq_left (Nat.le_of_lt hyx), if_neg (Nat.not_lt.2 (Nat.le_of_lt hyx))] at hμ; omega
  refine karLt impl R n0 ihK S hJ hA h40 hyx hμk fun Lk bk S1 hka => ?_
  refine lclr impl hap R hmc S1 hka fun P hlp => ?_
  refine lnat impl hap R hgr hmc hwb hlp fun Lk' bk' tp tl tc S2 hH => ?_
  exact lloop impl hap R hmv n0 ihM hμ (fun Lk bk k tp tl tc S hH hge => lend impl hl4 hl48 Lk bk k tp tl tc S hH hge)
    _ Lk' bk' 0 tp tl tc S2 (Nat.le_refl _) hH

end FvModexp.Arm64.Q.NatMul
