import FvModexp.Proofs.Amd64.NatQ.DivRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivCmp.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64), `len v ≥ 2`: entry → `u.cmp(v)`'s entry (natdiv.go:518-532)

Prologue (`fn + 0`): stack check, `PUSHQ BP`, `SUBQ $0xe0`, spills of `RAX`/`RSI`, the defer record pointer, the defer
bit and the result slots zeroed; `len v` (`[SP + 40]`) `≠ 0` and `≠ 1`; spills of `z`, `stk`, `z2`; `CALL nat.cmp` at
`fn + 0x1ca` with `u = (RAX, RBX, RCX)`, `v = (RDI, RSI, R8)` (the return address `retC` at `SP - 240`). Port of
`Arm64/Nat/DivCmp.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

/-- the frame ranges written before the `nat.cmp` call -/
@[reducible] def proW (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232), ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120),
    ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 16, (s.regs 4).toNat),
    ((s.regs 4).toNat + 56, (s.regs 4).toNat + 112)]

/-- the state at `nat.cmp`'s entry -/
structure AtK (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s X : State) : Prop where
  pc : X.rip = BitVec.ofNat 64 cmpE
  sp : X.regs 4 = s.regs 4 - 240#64
  r5 : X.regs 5 = s.regs 4 - 8#64
  r14 : X.regs 14 = s.regs 14
  fs : X.fsBase = s.fsBase
  x15 : X.xmm 15 = 0#128
  df : X.df = false
  a0 : X.regs 0 = BitVec.ofNat 64 u
  a3 : X.regs 3 = BitVec.ofNat 64 ul
  a1 : X.regs 1 = BitVec.ofNat 64 uc
  a7 : X.regs 7 = BitVec.ofNat 64 v
  a6 : X.regs 6 = BitVec.ofNat 64 vl
  a8 : X.regs 8 = BitVec.ofNat 64 vc
  rc : X.mem.readLE ((s.regs 4).toNat - 240) 8 = retC
  mf : MemFrame s.mem X.mem (proW s)
  reg : X.mem.regions = s.mem.regions
  bp : X.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  s1 : X.mem.readLE ((s.regs 4).toNat + 56) 8 = zp
  s2 : X.mem.readLE ((s.regs 4).toNat + 64) 8 = zl
  s3 : X.mem.readLE ((s.regs 4).toNat + 72) 8 = zc
  s4 : X.mem.readLE ((s.regs 4).toNat + 80) 8 = st
  s5 : X.mem.readLE ((s.regs 4).toNat + 88) 8 = z2
  s6 : X.mem.readLE ((s.regs 4).toNat + 96) 8 = z2l
  s7 : X.mem.readLE ((s.regs 4).toNat + 104) 8 = z2c
  q0 : X.mem.readLE ((s.regs 4).toNat - 16) 8 = 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `nat.cmp`'s entry (`len v ≥ 2`) -/
theorem two1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = z2)
    (h8 : s.regs 8 = z2l) (h9 : s.regs 9 = z2c) (hv2 : 2 ≤ vl)
    (hpre : Pre R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
    (Q : State → Prop)
    (k : ∀ X : State, AtK zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s X →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) s Q := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have r1 := hp.ru; have r2 := hp.rul; have r3 := hp.ruc; have r4 := hp.rv; have r5 := hp.rvl; have r6 := hp.rvc
  have hvl : vl < 2 ^ 40 := hp.vo.1
  have hul : ul < 2 ^ 40 := hp.uo.1
  have hv0 : (BitVec.ofNat 64 vl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
  have hv1 : (BitVec.ofNat 64 vl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  clear hpre hp
  janus64_run [r1, r2, r3, r4, r5, r6, hv0, hv1] until [cmpE]
  refine k _
    { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, a0 := ?_, a3 := ?_, a1 := ?_,
      a7 := ?_, a6 := ?_, a8 := ?_, rc := ?_, mf := ?qF, reg := ?qR, bp := ?_, s1 := ?_, s2 := ?_, s3 := ?_,
      s4 := ?_, s5 := ?_, s6 := ?_, s7 := ?_, q0 := ?_ }
  case qF => unfold proW; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals first | exact hx15 | exact hdf | (janus64_simp; omega) | rfl

end FvModexp.Amd64.Q.NatDiv
