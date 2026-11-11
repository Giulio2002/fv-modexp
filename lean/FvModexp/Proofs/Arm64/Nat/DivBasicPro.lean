import FvModexp.Proofs.Arm64.Nat.DivBasicCallees

/-!
# `divBasic` (arm64): the prologue — `defer stk.restore(stk.save())`, up to `CALL (*stack).nat` (natdiv.go:647-651)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0x80

/-- the frame ranges written before `CALL (*stack).nat` -/
@[reducible] def proWs (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 248, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 88)]

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s P : State) : Prop where
  pc : P.pc = BitVec.ofNat 64 callNat
  sp : P.sp = s.sp - 240#64
  r28 : P.regs 28 = s.regs 28
  r29 : P.regs 29 = s.sp - 248#64
  r18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (vl + 1)
  fr : MemFrame s.mem P.mem (proWs s)
  reg : P.mem.regions = s.mem.regions
  lr : P.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat
  fp : P.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat
  dbit : P.mem.readLE (s.sp.toNat - 137) 1 = 1
  mm : P.mem.readLE (s.sp.toNat - 88) 8 = (ul + 2 ^ 64 - vl) % 2 ^ 64
  n1 : P.mem.readLE (s.sp.toNat - 64) 8 = vl - 1
  dfn : P.mem.readLE (s.sp.toNat - 40) 8 = dfnA
  dst : P.mem.readLE (s.sp.toNat - 32) 8 = st
  dn : P.mem.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : P.mem.readLE (s.sp.toNat + 8) 8 = qp
  s2 : P.mem.readLE (s.sp.toNat + 16) 8 = ql
  s4 : P.mem.readLE (s.sp.toNat + 40) 8 = up
  s5 : P.mem.readLE (s.sp.toNat + 48) 8 = ul
  s6 : P.mem.readLE (s.sp.toNat + 56) 8 = uc
  s7 : P.mem.readLE (s.sp.toNat + 64) 8 = vp
  s8 : P.mem.readLE (s.sp.toNat + 72) 8 = vl
  s9 : P.mem.readLE (s.sp.toNat + 80) 8 = vc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- entry → `CALL (*stack).nat` -/
theorem pro1 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc vp vl vc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (h0 : s.regs 0 = qp) (h1 : s.regs 1 = ql) (h2 : s.regs 2 = qc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = up)
    (h5 : s.regs 5 = ul) (h6 : s.regs 6 = uc) (h7 : s.regs 7 = vp) (h8 : s.regs 8 = vl) (h9 : s.regs 9 = vc)
    (hpre : Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat s)
    (Q : State → Prop)
    (k : ∀ P, AtNat R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp.toNat vl.toNat vc.toNat s P →
      R.inv b L (s.regs 28).toNat (view R.rt L P.mem) → ReachesRet (LibDivBasic.program.link impl) (s.regs 30) P Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) s Q := by
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce
  have hstok := hpre.stok
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hstok
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hv2 := hpre.v2
  have hlen := hpre.stlen
  janus_run until [callNat]
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?qI
  case qF => unfold proWs; janus_frame
  case qR => simp only [Memory.regions_writeLE]
  case qI =>
    refine RtInv.inv_frame' (ws := proWs s) (by unfold proWs; janus_frame) (fun r hr => ?_) hpre.inv
    simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try (janus_simp; done)
  all_goals (janus_simp; try omega)
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; try omega)

end FvModexp.Arm64.DivBasic
