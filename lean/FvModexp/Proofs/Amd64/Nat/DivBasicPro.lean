import FvModexp.Proofs.Amd64.Nat.DivBasicCallees

set_option autoImplicit false

/-!
# `divBasic` (amd64): the prologue — `defer stk.restore(stk.save())`, up to `CALL (*stack).nat` (natdiv.go:647-651)

The twin of `Arm64/Nat/DivBasicPro.lean`. Code `+0x0 … +0xaf`: stack check, `PUSHQ BP; SUBQ $0xd8, SP`, spills of
`q.ptr, q.len, u`, `n - 1` at `RSP - 64`, `m = len u - n` at `RSP - 104`, the defer record, `CALL (*stack).nat`
with `RAX = stk`, `RBX = n + 1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0xaf

/-- the frame ranges written before `CALL (*stack).nat` (coarse) -/
@[reducible] def proWs (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 137, (s.regs 4).toNat), ((s.regs 4).toNat + 32, (s.regs 4).toNat + 88)]

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl : Nat) (s P : State) : Prop where
  pc : P.rip = BitVec.ofNat 64 callNat
  sp : P.regs 4 = s.regs 4 - 224#64
  r5 : P.regs 5 = s.regs 4 - 8#64
  r14 : P.regs 14 = s.regs 14
  fs : P.fsBase = s.fsBase
  x15 : P.xmm 15 = 0#128
  df : P.df = false
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r3 : P.regs 3 = BitVec.ofNat 64 (vl + 1)
  fr : MemFrame s.mem P.mem (proWs s)
  reg : P.mem.regions = s.mem.regions
  bp : P.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : P.mem.readLE ((s.regs 4).toNat - 137) 1 = 1
  mm : P.mem.readLE ((s.regs 4).toNat - 104) 8 = (ul + 2 ^ 64 - vl) % 2 ^ 64
  n1 : P.mem.readLE ((s.regs 4).toNat - 64) 8 = vl - 1
  dfn : P.mem.readLE ((s.regs 4).toNat - 40) 8 = dfnA
  dst : P.mem.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : P.mem.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  s1 : P.mem.readLE ((s.regs 4).toNat + 32) 8 = qp
  s2 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = ql
  s4 : P.mem.readLE ((s.regs 4).toNat + 64) 8 = up
  s5 : P.mem.readLE ((s.regs 4).toNat + 72) 8 = ul
  s6 : P.mem.readLE ((s.regs 4).toNat + 80) 8 = uc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- entry → `CALL (*stack).nat` -/
theorem pro1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (qp ql qc st up ul uc : BitVec 64) (vp vl : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = qp) (h3 : s.regs 3 = ql) (h1 : s.regs 1 = qc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = up)
    (h8 : s.regs 8 = ul) (h9 : s.regs 9 = uc)
    (hpre : Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s)
    (Q : State → Prop)
    (k : ∀ P, AtNat R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s P →
      R.inv b L (s.regs 14).toNat (view R.rt L P.mem) → ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) P Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) s Q := by
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hstok := hpre.stok
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hstok
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hv2 := hpre.v2
  have hlen := hpre.stlen
  have hvl := hpre.vlS
  have hvlb : vl < 2 ^ 16 := by omega
  have hstacc8 : s.mem.accessible (st.toNat + 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hstacc (by omega) (by omega))
  janus64_run [hvl, hstacc8] until [callNat]
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?qI
  case qF => unfold proWs; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  case qI =>
    refine RtInv.inv_frame' (ws := proWs s) (by unfold proWs; janus_frame) (fun r hr => ?_) hpre.inv
    simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try (janus64_simp; done)
  all_goals (janus64_simp; try omega)
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; try omega)

end FvModexp.Amd64.DivBasic
