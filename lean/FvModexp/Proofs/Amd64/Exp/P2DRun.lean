import FvModexp.Proofs.Amd64.Exp.P2DEnt

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): the runs that return without a call (agent asm s66; amd64 twin of infra's arm64
`P2DZero.zeroR`/`zero2` and `P2DOneR`'s `oneR0`/`oneR1`)

Frame base `sp` (`RSP = sp`, `[sp + 0x68]` = saved `BP`, `[sp + 0x70]` = return address `ret0`). Exits through the
epilogue `ADDQ $0x68, SP; POPQ BP; RET` with `Epi` (RSP = sp + 0x78, RBP = bp, R14 / FS base / X15 / DF kept):
* `zeroR`: `zeroE = 0x5e9025` (even `x`, `len y > 1`): `BX = 0`, `AX`/`CX` kept, memory kept;
* `zero2R`: `zero2 = 0x5e916a` (`tz · y[0]` overflows or `≥ logM`): `AX := R13` (= the spilled `z.ptr`), `BX = 0`;
* `oneR0`: `oneE` with `x[0]` even: `BX = 0`; `oneR1`: `x[0]` odd and `cap z ≠ 0`: `[z] := 1`, `BX = 1`;
* `oneRM`: `x[0]` odd, `cap z = 0`: to `makeslice`'s entry (`AX = Word type`, `BX = CX = 1`, return `mkRa`);
  `mkR`: from `mkRa`: `[AX] := 1`, `BX = CX = 1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

abbrev zero2 : Nat := 0x5e916a
abbrev mkRa : Nat := 0x5e910d
abbrev mkE : Nat := 0x485340
abbrev wordTy : Nat := 0x6e5ea0

theorem mkE_eq : Extracted.program.contractAddr "runtime.makeslice" = mkE := by decide

/-- the epilogue's register facts at the return -/
@[reducible] def Epi (S s' : State) (sp bp : Nat) : Prop :=
  s'.regs 4 = BitVec.ofNat 64 (sp + 0x78) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = S.regs 14 ∧
    s'.fsBase = S.fsBase ∧ s'.xmm 15 = S.xmm 15 ∧ s'.df = S.df

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {sp bp : Nat} {S : State}

theorem sp78 (h : sp + 0x78 ≤ 2 ^ 48) : BitVec.ofNat 64 sp + 120#64 = BitVec.ofNat 64 (sp + 0x78) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem zeroR (hpc : S.rip = BitVec.ofNat 64 zeroE) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hsp : sp + 0x78 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hr : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 0 → s'.regs 3 = 0#64 → s'.regs 1 = S.regs 1 →
      s'.mem = S.mem → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e := sp78 hsp
  janus64_run [hbp, hr]
  refine K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem zero2R (hpc : S.rip = BitVec.ofNat 64 zero2) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hsp : sp + 0x78 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hr : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 13 → s'.regs 3 = 0#64 → s'.regs 1 = S.regs 1 →
      s'.mem = S.mem → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have e := sp78 hsp
  janus64_run [hbp, hr]
  refine K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem oneR0 {xp xl : Nat} (hpc : S.rip = BitVec.ofNat 64 oneE) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hsp : sp + 0x78 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hr : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (hxl : 0 < xl) (hxl' : xl < 2 ^ 64)
    (hxa : S.mem.accessible xp 8 false = true) (hxp : xp + 8 ≤ 2 ^ 48) (hx0 : S.mem.readLE xp 8 % 2 = 0)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 0 → s'.regs 3 = 0#64 → s'.regs 1 = S.regs 1 →
      s'.mem = S.mem → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hb := (bit0_iff' (S.mem.readLE xp 8)).2 hx0
  have e := sp78 hsp
  janus64_run [hbp, hr, hb]
  refine K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem oneR1 {zp zc xp xl : Nat} (hpc : S.rip = BitVec.ofNat 64 oneE) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hsp : sp + 0x78 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hr : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zc) (hzc : 0 < zc) (hzc' : zc < 2 ^ 64)
    (hza : S.mem.accessible zp 8 true = true) (hzp : zp + 8 ≤ 2 ^ 48)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (hxl : 0 < xl) (hxl' : xl < 2 ^ 64)
    (hxa : S.mem.accessible xp 8 false = true) (hxp : xp + 8 ≤ 2 ^ 48) (hx0 : S.mem.readLE xp 8 % 2 = 1)
    (hzw : zp + 8 ≤ sp + 0x68 ∨ sp + 0x78 ≤ zp)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 0 → s'.regs 3 = 1#64 → s'.regs 1 = S.regs 1 →
      s'.mem = S.mem.writeLE zp 8 1 → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hb := (bit0_iff (S.mem.readLE xp 8)).2 hx0
  have hbp' : (S.mem.writeLE zp 8 1).readLE (sp + 0x68) 8 = bp := by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hbp
  have hr' : (S.mem.writeLE zp 8 1).readLE (sp + 0x70) 8 = ret0.toNat := by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hr
  have e := sp78 hsp
  janus64_run [hbp', hr', hb]
  refine K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem oneRM {xp xl : Nat} (hpc : S.rip = BitVec.ofNat 64 oneE) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hsp : 8 ≤ sp) (hsp' : sp + 0x78 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp - 8) 8 true = true)
    (h1 : S.regs 1 = 0#64)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (hxl : 0 < xl) (hxl' : xl < 2 ^ 64)
    (hxa : S.mem.accessible xp 8 false = true) (hxp : xp + 8 ≤ 2 ^ 48) (hx0 : S.mem.readLE xp 8 % 2 = 1)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 mkE → s'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      s'.regs 0 = BitVec.ofNat 64 wordTy → s'.regs 3 = 1#64 → s'.regs 1 = 1#64 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.fsBase = S.fsBase → s'.xmm 15 = S.xmm 15 → s'.df = S.df →
      s'.mem = S.mem.writeLE (sp - 8) 8 mkRa → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hb := (bit0_iff (S.mem.readLE xp 8)).2 hx0
  have e8 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [e8, hb] until [mkE]
  refine K _ rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl rfl rfl ?_
  janus64_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem mkR {p : Nat} (hpc : S.rip = BitVec.ofNat 64 mkRa) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (hsp : sp + 0x78 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp + 0x68) 16 false = true)
    (hbp : S.mem.readLE (sp + 0x68) 8 = bp) (hr : S.mem.readLE (sp + 0x70) 8 = ret0.toNat) (hret : ret0.toNat < 2 ^ 47)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (hpa : S.mem.accessible p 8 true = true) (hp48 : p + 8 ≤ 2 ^ 48)
    (hpw : p + 8 ≤ sp + 0x68 ∨ sp + 0x78 ≤ p)
    (K : ∀ s', Epi S s' sp bp → s'.regs 0 = S.regs 0 → s'.regs 3 = 1#64 → s'.regs 1 = 1#64 →
      s'.mem = S.mem.writeLE p 8 1 → Q s') :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hbp' : (S.mem.writeLE p 8 1).readLE (sp + 0x68) 8 = bp := by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hbp
  have hr' : (S.mem.writeLE p 8 1).readLE (sp + 0x70) 8 = ret0.toNat := by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hr
  have e := sp78 hsp
  janus64_run [hbp', hr']
  refine K _ ⟨by janus64_simp; exact e, by janus64_simp, rfl, rfl, rfl, rfl⟩ (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl

end

end FvModexp.Amd64.P2D
