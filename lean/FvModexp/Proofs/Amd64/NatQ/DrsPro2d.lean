import FvModexp.Proofs.Amd64.NatQ.DrsAt

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64), big path: the dispatch → `CALL (*stack).nat(stk, B + 1)` (natdiv.go:767-781)

From `dTest` (`0x5ef910`) with `0 < len u`, `40 ≤ n ≤ len u`: `TESTQ R8, R8` / `CMPQ divRecursiveThreshold, R11; JG`
(not taken) / `SUBQ R11, R8; JL` (not taken, `m = len u - n`), the spills (`r + 32 … + 88` = `z`, `stk`, `u.ptr`, `u.cap`,
`depth`; `r - 216` = `m`, `r - 192` = `n`, `r - 104` = `len u`, `r - 168` = `B = n / 2`), the defer record
`{deferwrap1, stk, len(stk.w)}` at `r - 56 / - 48 / - 40`, its pointer at `r - 16`, the defer bit at `r - 297`, and
`AX = stk`, `BX = B + 1` at the call `0x5ef9d8`. `AtN0`: the facts there. Twin of Arm64/NatQ/DrsPro2.lean `pro2d`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

/-- the facts at `CALL (*stack).nat(stk, B + 1)` (`0x5ef9d8`), entry state `s` (`r = RSP` at the entry) -/
structure AtN0 (s P : State) (qp ql qc st up ul uc vp vl vc d : Nat) : Prop where
  pc : P.rip = BitVec.ofNat 64 0x5ef9d8
  fr : Fr s P
  x15 : P.xmm 15 = 0#128
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r3 : P.regs 3 = BitVec.ofNat 64 (vl / 2 + 1)
  dbit : P.mem.readLE ((s.regs 4).toNat - 297) 1 = 1
  dfn : P.mem.readLE ((s.regs 4).toNat - 56) 8 = 0x5f0800
  dst : P.mem.readLE ((s.regs 4).toNat - 48) 8 = st
  dn : P.mem.readLE ((s.regs 4).toNat - 40) 8 = stLen s.mem st
  dp : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 56
  mm : P.mem.readLE ((s.regs 4).toNat - 216) 8 = ul - vl
  nn : P.mem.readLE ((s.regs 4).toNat - 192) 8 = vl
  uu : P.mem.readLE ((s.regs 4).toNat - 104) 8 = ul
  bb : P.mem.readLE ((s.regs 4).toNat - 168) 8 = vl / 2
  s1 : P.mem.readLE ((s.regs 4).toNat + 32) 8 = qp
  s2 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = ql
  s3 : P.mem.readLE ((s.regs 4).toNat + 48) 8 = qc
  s4 : P.mem.readLE ((s.regs 4).toNat + 56) 8 = st
  s5 : P.mem.readLE ((s.regs 4).toNat + 64) 8 = up
  s7 : P.mem.readLE ((s.regs 4).toNat + 80) 8 = uc
  s9 : P.mem.readLE ((s.regs 4).toNat + 88) 8 = d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `0 < len u`, `40 ≤ n ≤ len u` → `CALL (*stack).nat(stk, B + 1)` -/
theorem pro2d (impl : List Amd64.Segment) (r : W64) {s P : State} {qp ql qc st up ul uc vp vl vc d : Nat}
    (hA : AtE2 s P qp ql qc st up ul uc vp vl vc d) (h0 : 0 < ul) (h40 : 40 ≤ vl) (hle : vl ≤ ul)
    (hq : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64) (hst : st + 24 ≤ 2 ^ 48) (hup : up < 2 ^ 64)
    (hul : ul < 2 ^ 40) (huc : uc < 2 ^ 64) (hvl : vl < 2 ^ 40) (hd : d < 2 ^ 64)
    (h400 : 400 ≤ (s.regs 4).toNat) (h48 : (s.regs 4).toNat + 96 ≤ 2 ^ 48)
    (hacc : P.mem.accessible ((s.regs 4).toNat - 400) 496 true = true)
    (hsta : P.mem.accessible (st + 8) 8 false = true) (hstl : P.mem.readLE (st + 8) 8 = stLen s.mem st)
    (hstout : st + 24 ≤ (s.regs 4).toNat - 400 ∨ (s.regs 4).toNat + 96 ≤ st)
    (hth : P.mem.readLE 0xb4ae88 8 = 40) (htha : P.mem.accessible 0xb4ae88 8 false = true) (Q : State → Prop)
    (k : ∀ P', AtN0 s P' qp ql qc st up ul uc vp vl vc d → ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  have hpc := hA.pc; have h8 := hA.r8; have h11 := hA.r11
  have hF := hA.fr
  have hsp0 := hF.sp
  have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp0, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hne : (BitVec.ofNat 64 ul = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hsub : (BitVec.ofNat 64 ul - BitVec.ofNat 64 vl).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    rw [Nat.mod_eq_of_lt (show ul < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show vl < 2 ^ 64 by omega)]; omega
  have h7 := hA.r7
  have e7 : (BitVec.ofNat 64 st).toNat = st := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hm8 : (st + 8) % 18446744073709551616 = st + 8 := Nat.mod_eq_of_lt (by omega)
  janus64_run [h8, h11, h7, e7, hm8, hth, hne, hsub, BitVec.msb_eq_decide] until [0x5ef9d8]
  have e2 : (BitVec.ofNat 64 vl >>> 1).toNat = vl / 2 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  refine k _ ⟨rfl, ⟨?sp, hF.r5, hF.r14, hF.fs, hF.df, ?qR, ?qF, ?ra, ?bp, ?vp, ?vl, ?vc⟩, hA.x15, ?r0, ?r3, ?dbit, ?dfn,
    ?dst, ?dn, ?dp, ?mm, ?nn, ?uu, ?bb, ?s1, ?s2, ?s3, ?s4, ?s5, ?s7, ?s9⟩
  case qF => exact mf_trans hF.fr (by unfold fw win; janus_frame)
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hF.reg
  case r3 =>
    simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, e2]; simp only [BitVec.toNat_ofNat]
  all_goals try (janus64_simp; done)
  all_goals janus64_simp
  case ra => exact hF.ra
  case bp => exact hF.bp
  case vp => exact hF.vp
  case vl => exact hF.vl
  case vc => exact hF.vc
  case mm => omega
  case bb => exact e2
  case s1 => rw [hA.r0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hq
  case s2 => rw [hA.r3, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hql
  case s3 => rw [hA.r1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hqc
  case s5 => rw [hA.r6, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hup
  case s7 => rw [hA.r9, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt huc
  case s9 => rw [hA.r10, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hd

end FvModexp.Amd64.Q.DivRec
