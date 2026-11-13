import FvModexp.Proofs.Amd64.NatQ.DivMGet
import FvModexp.Proofs.Amd64.NatQ.DivBigRel
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Amd64.Nat.StkTyData

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`: from `Get`'s return to `divLarge`'s entry (nat.go:287-289, natdiv.go:539-543) (top s41)

Twin of Arm64/NatQ/DivMJoin.lean. `RSP = sp - 232` throughout (`sp` = the entry `RSP`).
* `getTM`: `Get` returned a pooled stack (`RAX = type:*big.stack`, `RBX = d ≠ 0`): `LEAQ; CMPQ AX, CX; JE`,
  `TESTQ BX; JNE` → `joinA`.
* `getNM`: `Get` returned nil (`RAX = RBX = 0`): `XORL BX`, `JNE` not taken, `LEAQ type:big.stack, AX`,
  `CALL runtime.newobject` (stops at its entry, return address `noR` at `sp - 240`).
* `noRetM`: `newobject`'s return (`RAX = p`): `MOVQ AX, BX` → `joinA`.
* `joinM`: from `joinA` (`RBX = d`): the defer record (`sp - 32 := nat.div.deferwrap1`, `sp - 24 := d`,
  `sp - 16 := sp - 32`, defer bits `sp - 121 := 1`, `sp - 122 := 1`), the argument reloads, `CALL divLarge` (stops
  at its entry, `AtLM`: as `AtL` with `st = d`, the defer record, the memory framed against the join state).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

/-- `nat.div.deferwrap1` -/
abbrev dwM : Nat := 0x5ee480

theorem dwM_eq : segAddr Extracted.program "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div.deferwrap1" = dwM := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `Get` returned a pooled stack `d ≠ 0` -/
theorem getTM (impl : List Amd64.Segment) (ret0 : BitVec 64) (Q : State → Prop) (d : Nat) (hd : d < 2 ^ 64)
    (hd0 : d ≠ 0) (S : State) (hpc : S.rip = BitVec.ofNat 64 getR) (h0 : S.regs 0 = BitVec.ofNat 64 Free.stkT)
    (h3 : S.regs 3 = BitVec.ofNat 64 d)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 joinA → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 3 = BitVec.ofNat 64 d → S'.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  have hd' : (BitVec.ofNat 64 d = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have h0' : S.regs 0 = 0x7170a0#64 := by rw [h0]; rfl
  janus64_run [h0', h3, hd'] until [joinA]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | (janus64_simp; done) | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `Get` returned nil: to `newobject(type:big.stack)`'s entry -/
theorem getNM (impl : List Amd64.Segment) (ret0 : BitVec 64) (Q : State → Prop) {s : State}
    (hb' : 41512 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 getR) (hsp : S.regs 4 = s.regs 4 - 232#64)
    (hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true)
    (h0 : S.regs 0 = 0#64) (h3 : S.regs 3 = 0#64)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 (cA "runtime.newobject") → X.regs 4 = s.regs 4 - 240#64 →
      X.regs 5 = S.regs 5 → X.regs 14 = S.regs 14 → X.fsBase = S.fsBase → X.xmm 15 = S.xmm 15 → X.df = S.df →
      X.regs 0 = BitVec.ofNat 64 stkTy →
      MemFrame S.mem X.mem [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232)] →
      X.mem.regions = S.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 240) 8 = noR →
      ReachesRet (LibDiv.program.link impl) ret0 X Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  janus64_run [h0, h3] until [cA "runtime.newobject"]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus_frame) ?_ ?_
  all_goals try (janus64_simp; done)
  all_goals first
    | rfl
    | (simp only [Janus.Arm64.Memory.regions_writeLE])
    | (simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]; rfl)
    | (janus64_simp; bv_omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `newobject`'s return (`RAX = p`) → `joinA` (`RBX = p`) -/
theorem noRetM (impl : List Amd64.Segment) (ret0 : BitVec 64) (Q : State → Prop) (p : Nat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 noR) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 joinA → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.regs 3 = BitVec.ofNat 64 p → S'.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  janus64_run [h0] until [joinA]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | (janus64_simp; done) | rfl

/-- the state at `divLarge`'s entry on the `stk == nil` path (`S` = the state at `joinA`) -/
structure AtLM (zp zl zc d z2 z2l z2c u ul uc v vl vc : Nat) (s S X : State) : Prop where
  pc : X.rip = BitVec.ofNat 64 divLE
  sp : X.regs 4 = s.regs 4 - 240#64
  r5 : X.regs 5 = S.regs 5
  r14 : X.regs 14 = S.regs 14
  fs : X.fsBase = S.fsBase
  x15 : X.xmm 15 = S.xmm 15
  df : X.df = S.df
  a0 : X.regs 0 = BitVec.ofNat 64 zp
  a3 : X.regs 3 = BitVec.ofNat 64 zl
  a1 : X.regs 1 = BitVec.ofNat 64 zc
  a7 : X.regs 7 = BitVec.ofNat 64 d
  a6 : X.regs 6 = BitVec.ofNat 64 z2
  a8 : X.regs 8 = BitVec.ofNat 64 z2l
  a9 : X.regs 9 = BitVec.ofNat 64 z2c
  rc : X.mem.readLE ((s.regs 4).toNat - 240) 8 = retL
  mf : MemFrame S.mem X.mem [((s.regs 4).toNat - 240, (s.regs 4).toNat - 184),
    ((s.regs 4).toNat - 122, (s.regs 4).toNat - 120), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 8)]
  reg : X.mem.regions = S.mem.regions
  by1 : X.mem.readLE ((s.regs 4).toNat - 122) 1 = 1
  dw : X.mem.readLE ((s.regs 4).toNat - 32) 8 = dwM
  dd : X.mem.readLE ((s.regs 4).toNat - 24) 8 = d
  dp : X.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32
  i0 : X.mem.readLE ((s.regs 4).toNat - 232) 8 = u
  i1 : X.mem.readLE ((s.regs 4).toNat - 224) 8 = ul
  i2 : X.mem.readLE ((s.regs 4).toNat - 216) 8 = uc
  i3 : X.mem.readLE ((s.regs 4).toNat - 208) 8 = v
  i4 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = vl
  i5 : X.mem.readLE ((s.regs 4).toNat - 192) 8 = vc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the defer record, the reloads, `CALL divLarge` -/
theorem joinM (impl : List Amd64.Segment) {zp zl zc z2 z2l z2c u ul uc v vl vc d : Nat} {s : State} {S : State}
    (hpc : S.rip = BitVec.ofNat 64 joinA) (hsp : S.regs 4 = s.regs 4 - 232#64) (h3 : S.regs 3 = BitVec.ofNat 64 d)
    (hd : d < 2 ^ 64) (hb' : 41512 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true)
    (m1 : S.mem.readLE ((s.regs 4).toNat + 56) 8 = zp) (m2 : S.mem.readLE ((s.regs 4).toNat + 64) 8 = zl)
    (m3 : S.mem.readLE ((s.regs 4).toNat + 72) 8 = zc) (m5 : S.mem.readLE ((s.regs 4).toNat + 88) 8 = z2)
    (m6 : S.mem.readLE ((s.regs 4).toNat + 96) 8 = z2l) (m7 : S.mem.readLE ((s.regs 4).toNat + 104) 8 = z2c)
    (m8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = u) (m9 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ul)
    (m10 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = uc) (m11 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = v)
    (m12 : S.mem.readLE ((s.regs 4).toNat + 40) 8 = vl) (m13 : S.mem.readLE ((s.regs 4).toNat + 48) 8 = vc)
    (ret0 : BitVec 64) (Q : State → Prop)
    (k : ∀ X, AtLM zp zl zc d z2 z2l z2c u ul uc v vl vc s S X → ReachesRet (LibDiv.program.link impl) ret0 X Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  have l8 : u < 2 ^ 64 := by rw [← m8]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l9 : ul < 2 ^ 64 := by rw [← m9]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l10 : uc < 2 ^ 64 := by rw [← m10]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l11 : v < 2 ^ 64 := by rw [← m11]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l12 : vl < 2 ^ 64 := by rw [← m12]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l13 : vc < 2 ^ 64 := by rw [← m13]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  janus64_run [h3, m1, m2, m3, m5, m6, m7, m8, m9, m10, m11, m12, m13] until [divLE]
  refine k _
    { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, a0 := ?_, a3 := ?_, a1 := ?_,
      a7 := ?_, a6 := ?_, a8 := ?_, a9 := ?_, rc := ?rc, mf := by janus_frame, reg := ?reg, by1 := ?by1,
      dw := ?dw, dd := ?dd, dp := ?dp, i0 := ?i0, i1 := ?i1, i2 := ?i2, i3 := ?i3, i4 := ?i4, i5 := ?i5 }
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals try rfl
  all_goals
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
      m8, m9, m10, m11, m12, m13]
  all_goals first
    | exact Nat.mod_eq_of_lt l8 | exact Nat.mod_eq_of_lt l9 | exact Nat.mod_eq_of_lt l10
    | exact Nat.mod_eq_of_lt l11 | exact Nat.mod_eq_of_lt l12 | exact Nat.mod_eq_of_lt l13
    | exact Nat.mod_eq_of_lt hd
    | (janus64_simp; omega)
    | (simp only [BitVec.toNat_ofNat, BitVec.toNat_sub]; omega)

end FvModexp.Amd64.Q.NatDiv
