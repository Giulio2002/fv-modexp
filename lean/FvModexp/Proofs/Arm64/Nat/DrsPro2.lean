import FvModexp.Proofs.Arm64.Nat.DrsPro

/-!
# `divRecursiveStep` (arm64): after `v.norm()` — the four ways on (natdiv.go:756-784)

`len(u) == 0` → `clear(z)` (`fn + 0x138`); `n < divRecursiveThreshold` (= 40, the global at `gA`) → `CALL divBasic`
(`fn + 0x128`); `m = len u - n < 0` → epilogue (`fn + 0x11c`); else `B = n/2`, `defer stk.restore(stk.save())` (record
`{deferwrap1, stk, len stk}` at `SP - 56 … SP - 40`, its address at `SP - 16`, defer bit byte `SP - 297` = 1), spills, and
`CALL (*stack).nat(stk, B + 1)` (`fn + 0x104`).

Slots (offsets from the entry `SP`): `m` `-208`, `n` `-184`, `len u` `-176`, `B` `-152`; spills `+8 … +88`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the state after `v.norm()` (`R5 = len u` normalised, `R8 = n`) -/
structure AtE2 (s P : State) (qp ql qc st up ul uc vp vl vc d : Nat) : Prop where
  pc : P.pc = BitVec.ofNat 64 nExit2
  fr : Fr s P
  r0 : P.regs 0 = BitVec.ofNat 64 qp
  r1 : P.regs 1 = BitVec.ofNat 64 ql
  r2 : P.regs 2 = BitVec.ofNat 64 qc
  r3 : P.regs 3 = BitVec.ofNat 64 st
  r4 : P.regs 4 = BitVec.ofNat 64 up
  r5 : P.regs 5 = BitVec.ofNat 64 ul
  r6 : P.regs 6 = BitVec.ofNat 64 uc
  r7 : P.regs 7 = BitVec.ofNat 64 vp
  r8 : P.regs 8 = BitVec.ofNat 64 vl
  r9 : P.regs 9 = BitVec.ofNat 64 vc
  r10 : P.regs 10 = BitVec.ofNat 64 d
  vlc : vl ≤ vc
  vc40 : vc < 2 ^ 40
  ul40 : ul < 2 ^ 40
  thr : P.mem.readLE 7147136 8 = 40
  thra : P.mem.accessible 7147136 8 false = true
  spn : P.sp.toNat = s.sp.toNat - 400
  sp0 : 408 ≤ s.sp.toNat
  sp48 : s.sp.toNat + 96 ≤ 2 ^ 48
  acc : P.mem.accessible (s.sp.toNat - 408) 504 true = true
  stacc : P.mem.accessible st 24 false = true
  st48 : st + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  stl : P.mem.readLE (st + 8) 8 = stLen s.mem st
  stout : st + 24 ≤ s.sp.toNat - 408 ∨ s.sp.toNat + 96 ≤ st

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `len(u) == 0` → `fn + 0x138` -/
theorem pro2a (impl : List Segment) (r : W64) {s P : State} {qp ql qc st up ul uc vp vl vc d : Nat}
    (hA : AtE2 s P qp ql qc st up ul uc vp vl vc d) (h0 : ul = 0) (Q : State → Prop)
    (k : ∀ P', P'.pc = BitVec.ofNat 64 0x1ba4d8 → P'.mem = P.mem → P'.sp = P.sp → P'.regs 0 = BitVec.ofNat 64 qp →
      P'.regs 1 = BitVec.ofNat 64 ql → P'.regs 28 = P.regs 28 → P'.regs 29 = P.regs 29 → P'.regs 18 = P.regs 18 →
      ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  subst h0
  have hpc := hA.pc; have h5 := hA.r5; have h8 := hA.r8; have h9 := hA.r9; have hvlc := hA.vlc; have hvc := hA.vc40
  have h0 := hA.r0; have h1 := hA.r1
  janus_run until [0x1ba4d8]
  exact k _ rfl rfl rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `0 < len u`, `n < 40` → `CALL divBasic` (`fn + 0x128`), arguments unchanged -/
theorem pro2b (impl : List Segment) (r : W64) {s P : State} {qp ql qc st up ul uc vp vl vc d : Nat}
    (hA : AtE2 s P qp ql qc st up ul uc vp vl vc d) (h0 : 0 < ul) (h40 : vl < 40) (Q : State → Prop)
    (k : ∀ P', P'.pc = BitVec.ofNat 64 0x1ba4c8 → P'.mem = P.mem → P'.sp = P.sp → (∀ j, j ≤ 10 → P'.regs j = P.regs j) →
      P'.regs 28 = P.regs 28 → P'.regs 29 = P.regs 29 → P'.regs 18 = P.regs 18 →
      ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  have hpc := hA.pc; have h5 := hA.r5; have h8 := hA.r8; have h9 := hA.r9; have hvlc := hA.vlc; have hvc := hA.vc40
  have hu40 := hA.ul40; have hth := hA.thr; have hta := hA.thra
  janus_run until [0x1ba4c8]
  refine k _ rfl rfl rfl ?_ (by janus_simp) (by janus_simp) (by janus_simp)
  intro j hj; try simp only [setReg]; repeat' rw [if_neg (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `0 < len u`, `40 ≤ n`, `len u < n` → the epilogue (`fn + 0x11c`) -/
theorem pro2c (impl : List Segment) (r : W64) {s P : State} {qp ql qc st up ul uc vp vl vc d : Nat}
    (hA : AtE2 s P qp ql qc st up ul uc vp vl vc d) (h0 : 0 < ul) (h40 : 40 ≤ vl) (hlt : ul < vl) (Q : State → Prop)
    (k : ∀ P', P'.pc = BitVec.ofNat 64 0x1ba4bc → P'.mem = P.mem → P'.sp = P.sp →
      P'.regs 28 = P.regs 28 → P'.regs 29 = P.regs 29 → P'.regs 18 = P.regs 18 →
      ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  have hpc := hA.pc; have h5 := hA.r5; have h8 := hA.r8; have h9 := hA.r9; have hvlc := hA.vlc; have hvc := hA.vc40
  have hu40 := hA.ul40; have hth := hA.thr; have hta := hA.thra
  have hneg : (BitVec.ofNat 64 ul - BitVec.ofNat 64 vl).msb = true := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hneg' : (BitVec.ofNat 64 ul - BitVec.ofNat 64 vl).getLsbD 63 = true := by
    rw [← hneg]; exact (BitVec.msb_eq_getLsbD_last _).symm
  janus_run [hneg'] until [0x1ba4bc]
  exact k _ rfl rfl rfl (by janus_simp) (by janus_simp) (by janus_simp)

/-- the facts at `CALL (*stack).nat(stk, B + 1)` (`fn + 0x104`), entry state `s` -/
structure AtN0 (s P : State) (qp ql qc st up ul uc vp vl vc d : Nat) : Prop where
  pc : P.pc = BitVec.ofNat 64 0x1ba4a4
  fr : Fr s P
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (vl / 2 + 1)
  mf : MemFrame s.mem P.mem (fw s)
  dbit : P.mem.readLE (s.sp.toNat - 297) 1 = 1
  dfn : P.mem.readLE (s.sp.toNat - 56) 8 = 0x1bae20
  dst : P.mem.readLE (s.sp.toNat - 48) 8 = st
  dn : P.mem.readLE (s.sp.toNat - 40) 8 = stLen s.mem st
  dp : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 56
  mm : P.mem.readLE (s.sp.toNat - 208) 8 = ul - vl
  nn : P.mem.readLE (s.sp.toNat - 184) 8 = vl
  ul' : P.mem.readLE (s.sp.toNat - 176) 8 = ul
  bb : P.mem.readLE (s.sp.toNat - 152) 8 = vl / 2
  s1 : P.mem.readLE (s.sp.toNat + 8) 8 = qp
  s2 : P.mem.readLE (s.sp.toNat + 16) 8 = ql
  s3 : P.mem.readLE (s.sp.toNat + 24) 8 = qc
  s4 : P.mem.readLE (s.sp.toNat + 32) 8 = st
  s5 : P.mem.readLE (s.sp.toNat + 40) 8 = up
  s7 : P.mem.readLE (s.sp.toNat + 56) 8 = uc
  s8 : P.mem.readLE (s.sp.toNat + 64) 8 = vp
  s10 : P.mem.readLE (s.sp.toNat + 80) 8 = vc
  s11 : P.mem.readLE (s.sp.toNat + 88) 8 = d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `0 < len u`, `40 ≤ n ≤ len u` → `CALL (*stack).nat(stk, B + 1)` -/
theorem pro2d (impl : List Segment) (r : W64) {s P : State} {qp ql qc st up ul uc vp vl vc d : Nat}
    (hA : AtE2 s P qp ql qc st up ul uc vp vl vc d) (h0 : 0 < ul) (h40 : 40 ≤ vl) (hle : vl ≤ ul)
    (hq : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64) (hst : st < 2 ^ 64) (hup : up < 2 ^ 64)
    (huc : uc < 2 ^ 64) (hvp : vp < 2 ^ 64) (hd : d < 2 ^ 64) (Q : State → Prop)
    (k : ∀ P', AtN0 s P' qp ql qc st up ul uc vp vl vc d → ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  have hpc := hA.pc; have h5 := hA.r5; have h8 := hA.r8; have h9 := hA.r9; have hvlc := hA.vlc; have hvc := hA.vc40
  have hu40 := hA.ul40; have hth := hA.thr; have hta := hA.thra
  have h0r := hA.r0; have h1r := hA.r1; have h2r := hA.r2; have h3r := hA.r3; have h4r := hA.r4; have h6r := hA.r6
  have h7r := hA.r7; have h10r := hA.r10; have hspn := hA.spn; have hsp0 := hA.sp0; have hsp48 := hA.sp48
  have hacc := hA.acc; have hsta := hA.stacc; have hst48 := hA.st48; have hstout := hA.stout
  have hF := hA.fr
  have hsp := hF.sp; have h28 := hF.r28; have h29 := hF.r29; have h18 := hF.r18
  have hal : (s.sp - 400#64).toNat % 16 = 0 := by
    have := hA.al; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hneg : (BitVec.ofNat 64 ul - BitVec.ofNat 64 vl).getLsbD 63 = false := by
    rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_decide]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hB := lsr1 vl (by omega)
  janus_run [hneg, hB] until [0x1ba4a4]
  refine k _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?qF1, ?_, ?_⟩, ?_, ?_, ?qF2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case qF1 => exact mf_trans hF.fr (by unfold fw winA; janus_frame)
  case qF2 => exact mf_trans hF.fr (by unfold fw winA; janus_frame)
  all_goals try (janus_simp; done)
  all_goals (janus_simp; try omega)
  · exact hF.reg
  · exact hF.lr
  · exact hF.fp
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · exact hA.stl

end FvModexp.Arm64.DivRec
