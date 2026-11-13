import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivMGet

set_option autoImplicit false

/-!
# `nat.div` (arm64), `stk == nil`: from `Get`'s return to `divLarge`'s entry (nat.go:287-289, natdiv.go:539-543)

* `getTD`: `Get` returned a pooled stack (`X0 = type:*big.stack`, `X1 = d ≠ 0`): `CMP`/`BEQ`, `CBNZ X1` → `joinA`.
* `getND`: `Get` returned nil (`X0 = X1 = 0`): `X1 := 0`, `CBNZ` not taken → `newobject(type:big.stack)` entry
  (`X30` = `noRD`).
* `noRetD`: `newobject`'s return (`X0 = p`) → `joinA` (`X1 := p`).
* `joinD`: from `joinA` (`X1 = d`): the defer record (`SP - 32 := nat.div.deferwrap1`, `SP - 24 := d`,
  `SP - 16 := SP - 32`, defer bits `SP - 121`, `SP - 122 := 1`), the argument reloads, `CALL divLarge` (stops at
  its entry, `X30 = retL`, `X3 = d`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

/-- the join point after `getStack()` (fn+0x278, `X1` = the stack) -/
abbrev joinA : Nat := 1807480
/-- `newobject`'s return point (fn+0x274) -/
abbrev noRD : Nat := 1807476
/-- the type descriptor `type:big.stack` (`newobject`'s argument) -/
abbrev stkTyD : Nat := Extracted.dataAddr.«type:big.stack#c761f19c»
/-- `nat.div.deferwrap1` -/
abbrev dwD : Nat := 1807776

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem getTD (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (d : Nat) (hd : d < 2 ^ 64) (hd0 : d ≠ 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 getRD) (h0 : S.regs 0 = BitVec.ofNat 64 Free.stkT)
    (h1 : S.regs 1 = BitVec.ofNat 64 d)
    (k : ∀ S' : State, S'.pc = BitVec.ofNat 64 joinA → S'.sp = S.sp → S'.regs 1 = BitVec.ofNat 64 d →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  have hd' : (BitVec.ofNat 64 d = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have h0' : S.regs 0 = 2841824#64 := by rw [h0]; rfl
  janus_run [hd', h0'] until [joinA]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | (janus_simp; done) | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem getND (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 getRD) (h0 : S.regs 0 = 0#64) (h1 : S.regs 1 = 0#64)
    (k : ∀ S' : State, S'.pc = BitVec.ofNat 64 (cA "runtime.newobject") → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 stkTyD → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.regs 30 = BitVec.ofNat 64 noRD → S'.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  janus_run [] until [cA "runtime.newobject"]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | (janus_simp; done) | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem noRetD (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop) (p : Nat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 noRD) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (k : ∀ S' : State, S'.pc = BitVec.ofNat 64 joinA → S'.sp = S.sp → S'.regs 1 = BitVec.ofNat 64 p →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  janus_run [] until [joinA]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | (janus_simp; done) | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the defer record, the reloads, `CALL divLarge` -/
theorem joinD (impl : List Segment) {zp zl zc z2 z2l z2c u ul uc v vl vc d : Nat} {s : State} {S : State}
    (hpc : S.pc = BitVec.ofNat 64 joinA) (hsp : S.sp = s.sp - 240#64) (h1 : S.regs 1 = BitVec.ofNat 64 d)
    (hd : d < 2 ^ 64)
    (hal : s.sp.toNat % 16 = 0) (hb' : 41504 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true)
    (m1 : S.mem.readLE (s.sp.toNat + 8) 8 = zp) (m2 : S.mem.readLE (s.sp.toNat + 16) 8 = zl)
    (m3 : S.mem.readLE (s.sp.toNat + 24) 8 = zc) (m5 : S.mem.readLE (s.sp.toNat + 40) 8 = z2)
    (m6 : S.mem.readLE (s.sp.toNat + 48) 8 = z2l) (m7 : S.mem.readLE (s.sp.toNat + 56) 8 = z2c)
    (m8 : S.mem.readLE (s.sp.toNat + 64) 8 = u) (m9 : S.mem.readLE (s.sp.toNat + 72) 8 = ul)
    (m10 : S.mem.readLE (s.sp.toNat + 80) 8 = uc) (m11 : S.mem.readLE (s.sp.toNat + 88) 8 = v)
    (m12 : S.mem.readLE (s.sp.toNat + 96) 8 = vl) (m13 : S.mem.readLE (s.sp.toNat + 104) 8 = vc)
    (Q : State → Prop)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivLarge.fn) → X.sp = S.sp →
      X.regs 28 = S.regs 28 → X.regs 29 = S.regs 29 → X.regs 18 = S.regs 18 →
      X.regs 30 = BitVec.ofNat 64 retL →
      X.regs 0 = BitVec.ofNat 64 zp → X.regs 1 = BitVec.ofNat 64 zl → X.regs 2 = BitVec.ofNat 64 zc →
      X.regs 3 = BitVec.ofNat 64 d → X.regs 4 = BitVec.ofNat 64 z2 → X.regs 5 = BitVec.ofNat 64 z2l →
      X.regs 6 = BitVec.ofNat 64 z2c → X.regs 7 = BitVec.ofNat 64 u → X.regs 8 = BitVec.ofNat 64 ul →
      X.regs 9 = BitVec.ofNat 64 uc → X.regs 10 = BitVec.ofNat 64 v → X.regs 11 = BitVec.ofNat 64 vl →
      X.regs 12 = BitVec.ofNat 64 vc →
      MemFrame S.mem X.mem [(s.sp.toNat - 122, s.sp.toNat - 120), (s.sp.toNat - 32, s.sp.toNat - 8)] →
      X.mem.regions = S.mem.regions → X.mem.readLE (s.sp.toNat - 122) 1 = 1 →
      X.mem.readLE (s.sp.toNat - 32) 8 = dwD → X.mem.readLE (s.sp.toNat - 24) 8 = d →
      X.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32 →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  janus_run [m1, m2, m3, m5, m6, m7, m8, m9, m10, m11, m12, m13] until [segAddr Extracted.program DivLarge.fn]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (simp only [Memory.regions_writeLE]; done) | (janus_frame; done) | (janus_simp; done) | skip
  all_goals (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod]; omega)

end FvModexp.Arm64.NatDiv
