import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivLargeDefs

/-!
# `divLarge` (arm64): the prologue — `defer stk.restore(stk.save())`, spills, up to `CALL (*stack).nat` (natdiv.go:597-607)

Offsets from the entry `SP` (`SP' = SP - 304`): saved `X30` `-304`, `X29` `-312`; defer bit byte `-201`; `vIn[n-1]` `-168`;
`len uIn + 1` `-136`; `m` `-128`; result slots `q` `-64 … -48`, `r` `-88 … -72` (zeroed); defer record
`{deferwrap1, stk, len(stk)}` at `-40, -32, -24`, its address at `-16`; spills `+8` zp, `+24` zc, `+32` st, `+40` up,
`+56` uc, `+64` ip, `+72` il, `+80` ic, `+88` vp, `+96` vl, `+104` vc.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivLarge

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0xc8

/-- `nat.divLarge.deferwrap1` -/
abbrev dfnL : Nat := 1810160

/-- the frame ranges written before `CALL (*stack).nat` -/
@[reducible] def proWs (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 312, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 112)]

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (st up uc ip il ic vp vl vc zp zc : Nat) (s P : State) : Prop where
  pc : P.pc = BitVec.ofNat 64 callNat
  sp : P.sp = s.sp - 304#64
  r28 : P.regs 28 = s.regs 28
  r29 : P.regs 29 = s.sp - 312#64
  r18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 vl
  fr : MemFrame s.mem P.mem (proWs s)
  reg : P.mem.regions = s.mem.regions
  lr : P.mem.readLE (s.sp.toNat - 304) 8 = (s.regs 30).toNat
  fp : P.mem.readLE (s.sp.toNat - 312) 8 = (s.regs 29).toNat
  dbit : P.mem.readLE (s.sp.toNat - 201) 1 = 1
  vtop : P.mem.readLE (s.sp.toNat - 168) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  il1 : P.mem.readLE (s.sp.toNat - 136) 8 = il + 1
  mm : P.mem.readLE (s.sp.toNat - 128) 8 = il - vl
  q0 : P.mem.readLE (s.sp.toNat - 64) 8 = 0
  q1 : P.mem.readLE (s.sp.toNat - 56) 8 = 0
  q2 : P.mem.readLE (s.sp.toNat - 48) 8 = 0
  t0 : P.mem.readLE (s.sp.toNat - 88) 8 = 0
  t1 : P.mem.readLE (s.sp.toNat - 80) 8 = 0
  t2 : P.mem.readLE (s.sp.toNat - 72) 8 = 0
  dfn : P.mem.readLE (s.sp.toNat - 40) 8 = dfnL
  dst : P.mem.readLE (s.sp.toNat - 32) 8 = st
  dn : P.mem.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : P.mem.readLE (s.sp.toNat + 8) 8 = zp
  s3 : P.mem.readLE (s.sp.toNat + 24) 8 = zc
  s4 : P.mem.readLE (s.sp.toNat + 32) 8 = st
  s5 : P.mem.readLE (s.sp.toNat + 40) 8 = up
  s7 : P.mem.readLE (s.sp.toNat + 56) 8 = uc
  s8 : P.mem.readLE (s.sp.toNat + 64) 8 = ip
  s9 : P.mem.readLE (s.sp.toNat + 72) 8 = il
  s10 : P.mem.readLE (s.sp.toNat + 80) 8 = ic
  s11 : P.mem.readLE (s.sp.toNat + 88) 8 = vp
  s12 : P.mem.readLE (s.sp.toNat + 96) 8 = vl
  s13 : P.mem.readLE (s.sp.toNat + 104) 8 = vc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- entry → `CALL (*stack).nat` -/
theorem pro1 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat)
    (zp zl zc st up ul uc ip il ic vp vl vc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = up)
    (h5 : s.regs 5 = ul) (h6 : s.regs 6 = uc) (h7 : s.regs 7 = ip) (h8 : s.regs 8 = il) (h9 : s.regs 9 = ic)
    (h10 : s.regs 10 = vp) (h11 : s.regs 11 = vl) (h12 : s.regs 12 = vc)
    (hpre : Pre R b L c zp.toNat zc.toNat st.toNat up.toNat uc.toNat ip.toNat il.toNat vp.toNat vl.toNat s)
    (Q : State → Prop)
    (k : ∀ P, AtNat st.toNat up.toNat uc.toNat ip.toNat il.toNat ic.toNat vp.toNat vl.toNat vc.toNat zp.toNat zc.toNat
      s P → R.inv b L (s.regs 28).toNat (view R.rt L P.mem) → ReachesRet (LibDivL.program.link impl) (s.regs 30) P Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) s Q := by
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce
  obtain ⟨⟨-, -, hstacc, hst48, -, -, -⟩, hsw, -, -⟩ := hpre.sti
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  obtain ⟨hv40, hvacc, hv48, -, hvw⟩ := hpre.vo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hv2 := hpre.v2
  have hvil := hpre.vil
  have hil9 := hpre.il9
  have hvr : (BitVec.ofNat 64 vl.toNat - 1#64).toNat = vl.toNat - 1 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus_run until [callNat]
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?qI
  case qF => unfold proWs; janus_frame
  case qR => simp only [Memory.regions_writeLE]
  case qI =>
    refine RtInv.inv_frame' (ws := proWs s) (by unfold proWs; janus_frame) (fun r hr => ?_) hpre.inv
    simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try (janus_simp; done)
  all_goals (janus_simp; omega)

end FvModexp.Arm64.DivLarge
