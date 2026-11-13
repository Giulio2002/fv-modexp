import FvModexp.Proofs.Amd64.NatQ.MulRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulMakeA1.lean — TIGHT COSTS] `nat.mul` (amd64), `m ≥ n ≥ 2`, `z` too small or an alias: up to the `makeslice` entry

`AA s S …`: the state at the `runtime.makeslice` entry (CALL at `0x5f0981`, return `0x5f0986`) with `AX = Word`'s type
descriptor, `BX = m + n`, `CX = m + n + 4`, the spills `0x70(SP') = m + n`, `0x58(SP') = m + n + 4`,
`0x138 .. 0x150(SP') = stk, x` (`SP' = RSP - 256`; the call pushed the return address at `RSP - 264`), `y` (stack
argument) at `RSP + 8 .. + 24`, memory changed in the window only. `alloc_head`: the run from the entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

/-- see the module doc -/
structure AA (s S : State) (W : Nat) (st xp xl xc yp yl yc : BitVec 64) : Prop where
  pc : S.rip = BitVec.ofNat 64 (cA "runtime.makeslice")
  r0 : S.regs 0 = BitVec.ofNat 64 NatAdd.wordT
  r3 : S.regs 3 = BitVec.ofNat 64 (xl.toNat + yl.toNat)
  r1 : S.regs 1 = BitVec.ofNat 64 (xl.toNat + yl.toNat + 4)
  sp : S.regs 4 = s.regs 4 - 264#64
  g : S.regs 14 = s.regs 14
  bp : S.regs 5 = s.regs 4 - 8#64
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  x15 : S.xmm 15 = s.xmm 15
  mret : S.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0986
  mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  m144 : S.mem.readLE ((s.regs 4).toNat - 144) 8 = xl.toNat + yl.toNat
  m168 : S.mem.readLE ((s.regs 4).toNat - 168) 8 = xl.toNat + yl.toNat + 4
  mst : S.mem.readLE ((s.regs 4).toNat + 56) 8 = st.toNat
  mxp : S.mem.readLE ((s.regs 4).toNat + 64) 8 = xp.toNat
  mxl : S.mem.readLE ((s.regs 4).toNat + 72) 8 = xl.toNat
  mxc : S.mem.readLE ((s.regs 4).toNat + 80) 8 = xc.toNat
  my1 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat
  my2 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat
  my3 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat
  F : MemFrame s.mem S.mem (win s W 88)
  reg : S.mem.regions = s.mem.regions

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc_head (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0840)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hy1 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat) (hy2 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat)
    (hy3 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hyl2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ S : State, AA s S W st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s Q := by
  obtain ⟨hce, hmw, -, -, -, ⟨⟨hxlc, hxc40, hxl12, -, hxh, -⟩, ⟨hylc, hyc40, hyl12, -, hyh, -⟩,
    ⟨hzc40, hzl, -, -, -, -⟩, -⟩, -, -, -, -⟩ := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  obtain ⟨-, hx48⟩ := hxh (by omega)
  obtain ⟨-, hy48⟩ := hyh (by omega)
  have hzl' : 0 < zc.toNat → zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 := fun h => (hzl h).2.2.2
  clear hzl hxh hyh hmw
  have hxy := toInt_small (yl + xl) (by rw [BitVec.toNat_add]; omega)
  janus64_run [hy1, hy2, hy3, BitVec.msb_eq_decide, toInt_small zc (by omega), toInt_small xl (by omega),
    toInt_small yl (by omega), hxy] until [cA "runtime.makeslice"]
  all_goals
    refine hK _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?F, ?_⟩
    case F => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first
      | omega
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.Q.NatMul
