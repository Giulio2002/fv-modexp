import FvModexp.Proofs.Amd64.Nat.DivLargeCallees

set_option autoImplicit false

/-!
# `divLarge` (amd64): the prologue — `defer stk.restore(stk.save())`, spills, up to `CALL (*stack).nat` (natdiv.go:597-607)

The twin of `Arm64/Nat/DivLargePro.lean`. Code `+0x0 … +0x120`: stack check, `PUSHQ BP; SUBQ $0x128, SP`, spills of
`z.ptr`, `z.cap`, `stk`, `u.ptr`, `u.cap` (`RSP + 56, 72, 80, 88, 104`), the zeroed result slots, the defer record,
`m = len uIn - n` (`RSP - 128`), `vIn[n-1]` (`RSP - 168`), `len uIn + 1` (`RSP - 136`), `CALL (*stack).nat` with
`RAX = stk`, `RBX = n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivLarge

/-- the `CALL (*stack).nat` -/
abbrev callNat : Nat := segAddr Extracted.program fn + 0x120

/-- the frame ranges written before `CALL (*stack).nat` (coarse) -/
@[reducible] def proWs (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 209, (s.regs 4).toNat), ((s.regs 4).toNat + 56, (s.regs 4).toNat + 112)]

/-- the facts at the `CALL (*stack).nat` (state `P`) -/
structure AtNat (st up uc il vp vl zp zc : Nat) (s P : State) : Prop where
  pc : P.rip = BitVec.ofNat 64 callNat
  sp : P.regs 4 = s.regs 4 - 304#64
  r5 : P.regs 5 = s.regs 4 - 8#64
  r14 : P.regs 14 = s.regs 14
  fs : P.fsBase = s.fsBase
  x15 : P.xmm 15 = 0#128
  df : P.df = false
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r3 : P.regs 3 = BitVec.ofNat 64 vl
  fr : MemFrame s.mem P.mem (proWs s)
  reg : P.mem.regions = s.mem.regions
  bp : P.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : P.mem.readLE ((s.regs 4).toNat - 209) 1 = 1
  vtop : P.mem.readLE ((s.regs 4).toNat - 168) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  il1 : P.mem.readLE ((s.regs 4).toNat - 136) 8 = il + 1
  mm : P.mem.readLE ((s.regs 4).toNat - 128) 8 = il - vl
  q0 : P.mem.readLE ((s.regs 4).toNat - 64) 8 = 0
  q1 : P.mem.readLE ((s.regs 4).toNat - 56) 8 = 0
  q2 : P.mem.readLE ((s.regs 4).toNat - 48) 8 = 0
  t0 : P.mem.readLE ((s.regs 4).toNat - 88) 8 = 0
  t1 : P.mem.readLE ((s.regs 4).toNat - 80) 8 = 0
  t2 : P.mem.readLE ((s.regs 4).toNat - 72) 8 = 0
  dfn : P.mem.readLE ((s.regs 4).toNat - 40) 8 = dfnL
  dst : P.mem.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : P.mem.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  s1 : P.mem.readLE ((s.regs 4).toNat + 56) 8 = zp
  s3 : P.mem.readLE ((s.regs 4).toNat + 72) 8 = zc
  s4 : P.mem.readLE ((s.regs 4).toNat + 80) 8 = st
  s5 : P.mem.readLE ((s.regs 4).toNat + 88) 8 = up
  s7 : P.mem.readLE ((s.regs 4).toNat + 104) 8 = uc

/-- the defer-bit test point `CMPQ BX, DX` (`+0xc0`, natdiv.go:606) -/
abbrev ptA : Nat := segAddr Extracted.program fn + 0xc0

/-- the facts at `ptA` (state `A`): the defer record and the zeroed result slots are written -/
structure AtA (st zp zc up uc il vl : Nat) (s A : State) : Prop where
  pc : A.rip = BitVec.ofNat 64 ptA
  sp : A.regs 4 = s.regs 4 - 304#64
  r5 : A.regs 5 = s.regs 4 - 8#64
  r14 : A.regs 14 = s.regs 14
  fs : A.fsBase = s.fsBase
  x15 : A.xmm 15 = 0#128
  df : A.df = false
  r0 : A.regs 0 = BitVec.ofNat 64 zp
  r1 : A.regs 1 = BitVec.ofNat 64 zc
  r6 : A.regs 6 = BitVec.ofNat 64 up
  r7 : A.regs 7 = BitVec.ofNat 64 st
  r9 : A.regs 9 = BitVec.ofNat 64 uc
  r3 : A.regs 3 = BitVec.ofNat 64 vl
  r2 : A.regs 2 = BitVec.ofNat 64 (vl - 1)
  r10 : A.regs 10 = BitVec.ofNat 64 (il - vl)
  r11 : A.regs 11 = BitVec.ofNat 64 il
  fr : MemFrame s.mem A.mem (proWs s)
  reg : A.mem.regions = s.mem.regions
  bp : A.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : A.mem.readLE ((s.regs 4).toNat - 209) 1 = 1
  q0 : A.mem.readLE ((s.regs 4).toNat - 64) 8 = 0
  q1 : A.mem.readLE ((s.regs 4).toNat - 56) 8 = 0
  q2 : A.mem.readLE ((s.regs 4).toNat - 48) 8 = 0
  t0 : A.mem.readLE ((s.regs 4).toNat - 88) 8 = 0
  t1 : A.mem.readLE ((s.regs 4).toNat - 80) 8 = 0
  t2 : A.mem.readLE ((s.regs 4).toNat - 72) 8 = 0
  dfn : A.mem.readLE ((s.regs 4).toNat - 40) 8 = dfnL
  dst : A.mem.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : A.mem.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : A.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → `ptA` (pure run: only register/stack facts) -/
theorem proA (impl : List Amd64.Segment) (R : RtInv) (L : List (Nat × Nat)) (st zp zc up uc : BitVec 64)
    (il vl : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = up) (h9 : s.regs 9 = uc)
    (hce : CallEnv R L s 41272 112)
    (hilS : s.mem.readLE ((s.regs 4).toNat + 16) 8 = il) (hvlS : s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl)
    (hstacc8 : s.mem.accessible (st.toNat + 8) 8 false = true) (hst48 : st.toNat + 24 ≤ 2 ^ 48)
    (hsw : st.toNat + 24 ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ st.toNat)
    (hv2 : 2 ≤ vl) (hvil : vl ≤ il) (hil9 : il ≤ 2 ^ 9) (Q : State → Prop)
    (k : ∀ A, AtA st.toNat zp.toNat zc.toNat up.toNat uc.toNat il vl s A →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) A Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  clear hLs hout hgr
  janus64_run [hilS, hvlS, hstacc8] until [ptA]
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  case qF => unfold proWs; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals (janus64_simp; try omega)
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; try omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `ptA` → `CALL (*stack).nat` (pure run from `AtA`) -/
theorem proB (impl : List Amd64.Segment) (st zp zc up uc : Nat) (il vp vl : Nat) (s A : State)
    (hA : AtA st zp zc up uc il vl s A)
    (hb' : 41272 ≤ (s.regs 4).toNat) (hs48 : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (hw : A.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true)
    (hvpS : A.mem.readLE ((s.regs 4).toNat + 32) 8 = vp)
    (hvt : A.mem.readLE (vp + 8 * (vl - 1)) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8)
    (hvtacc : A.mem.accessible (vp + 8 * (vl - 1)) 8 false = true) (hv48 : vp + 8 * vl ≤ 2 ^ 48)
    (hvw : vp + 8 * vl ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ vp)
    (hv2 : 2 ≤ vl) (hvil : vl ≤ il) (hil9 : il ≤ 2 ^ 9) (hz : zp < 2 ^ 64) (hzc : zc < 2 ^ 64) (hu : up < 2 ^ 64)
    (huc : uc < 2 ^ 64) (hst : st < 2 ^ 64) (Q : State → Prop)
    (k : ∀ P, AtNat st up uc il vp vl zp zc s P → ReachesRet (LibDivL.program.link impl) (retAddrOf s) P Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) A Q := by
  obtain ⟨hpc, hsp, h5, h14, hfs, hx, hdf, r0, r1, r6, r7, r9, r3, r2, r10, r11, hF, hreg, hbp, hdb, hq0, hq1, hq2,
    ht0, ht1, ht2, hdfn, hdst, hdn, hdp⟩ := hA
  have hspN : (A.regs 4).toNat = (s.regs 4).toNat - 304 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hvl' : vl % 2 ^ 64 = vl := Nat.mod_eq_of_lt (by omega)
  have hvp' : vp % 2 ^ 64 = vp := Nat.mod_eq_of_lt (by omega)
  have e1 : (BitVec.ofNat 64 vl * 8#64).toNat = 8 * vl := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; rw [hvl', Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
  have hva : (BitVec.ofNat 64 vp + BitVec.ofNat 64 vl * 8#64 + 18446744073709551608#64).toNat = vp + 8 * (vl - 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_add, e1]; simp only [BitVec.toNat_ofNat]; rw [hvp']
    rw [Nat.mod_eq_of_lt (show vp + 8 * vl < 2 ^ 64 by omega)]; omega
  have hacc : ∀ a n v, A.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  janus64_run [hvpS, hvtacc, hva, hvt] until [callNat]
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?qV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case qF => unfold proWs at hF ⊢; janus_frame
  case qV =>
    dsimp only
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      show vp + vl * 8 - 8 = vp + 8 * (vl - 1) by omega]
    have := Janus.Arm64.Memory.readLE_lt s.mem (vp + 8 * (vl - 1)) 8
    exact Nat.mod_eq_of_lt (by simpa using this)
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hreg
  all_goals try (janus64_simp; done)
  all_goals (janus64_simp; try omega)
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; try omega)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → `CALL (*stack).nat` -/
theorem pro1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat)
    (zp zl zc st up ul uc : BitVec 64) (ip il vp vl : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = up)
    (h8 : s.regs 8 = ul) (h9 : s.regs 9 = uc)
    (hpre : Pre R b L c zp.toNat zc.toNat st.toNat up.toNat uc.toNat ip il vp vl s)
    (Q : State → Prop)
    (k : ∀ P, AtNat st.toNat up.toNat uc.toNat il vp vl zp.toNat zc.toNat s P →
      R.inv b L (s.regs 14).toNat (view R.rt L P.mem) → ReachesRet (LibDivL.program.link impl) (retAddrOf s) P Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) s Q := by
  have hce := hpre.ce
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨⟨-, -, hstacc, hst48, -, -, -⟩, hsw, -, -⟩ := hpre.sti
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  obtain ⟨hv40, hvacc, hv48, -, hvw⟩ := hpre.vo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  have hv2 := hpre.v2
  have hvil := hpre.vil
  have hil9 := hpre.il9
  have hstacc8 : s.mem.accessible (st.toNat + 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hstacc (by omega) (by omega))
  refine proA impl R L st zp zc up uc il vl s hpc hx15 hdf h0 h1 h7 h6 h9 hce hpre.ilS hpre.vlS hstacc8 hst48
    (by omega) hv2 hvil hil9 Q fun A hA => ?_
  have hF := hA.fr
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 209 ∨ (s.regs 4).toNat ≤ a ∧ a + n ≤ (s.regs 4).toNat + 56 ∨
      (s.regs 4).toNat + 112 ≤ a) → A.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
  have hvt : A.mem.readLE (vp + 8 * (vl - 1)) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8 := hrd _ _ (by omega)
  have hvtacc : A.mem.accessible (vp + 8 * (vl - 1)) 8 false = true := by
    rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hvacc (by omega) (by omega)
  have hwA : A.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hF.accessible]; exact hw
  have hvpA : A.mem.readLE ((s.regs 4).toNat + 32) 8 = vp := by rw [hrd _ _ (by omega)]; exact hpre.vpS
  refine proB impl st.toNat zp.toNat zc.toNat up.toNat uc.toNat il vp vl s A hA hb' (by omega) hwA hvpA hvt hvtacc hv48 hvw
    hv2 hvil hil9 zp.isLt zc.isLt up.isLt uc.isLt st.isLt Q fun P hP => k P hP ?_
  refine RtInv.inv_frame' (ws := proWs s) hP.fr (fun r hr => ?_) hpre.inv
  simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))


end FvModexp.Amd64.DivLarge
