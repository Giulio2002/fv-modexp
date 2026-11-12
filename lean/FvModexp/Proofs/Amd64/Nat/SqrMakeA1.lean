import FvModexp.Proofs.Amd64.Nat.SqrRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.sqr` (amd64), `make_alloc` head: the state at the `makeslice` call `0x5f1101`

`AA s S …`: after the prologue and the alias / capacity test (natmul.go:85-88) every allocating path reaches `makeslice`'s
entry (CALL at `0x5f1101`, return `0x5f1106`) with `AX = Word`'s type descriptor, `BX = 2n`, `CX = 2n + 4`, the spills
`0x58(SP') = 2n`, `0x50(SP') = 2n + 4`, `0xc8..0xe0(SP') = stk, x` (`SP' = RSP - 168`; the call pushed the return address
at `RSP - 176`), memory changed in the window only. `alloc_head`: the run from the entry. Twin of arm64 SqrMakeAD/SqrMakeA1
(divmc s32).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSqr

/-- see the module doc -/
structure AA (s S : State) (W : Nat) (st xp xl xc : BitVec 64) : Prop where
  pc : S.rip = BitVec.ofNat 64 (cA "runtime.makeslice")
  r0 : S.regs 0 = BitVec.ofNat 64 NatAdd.wordT
  r3 : S.regs 3 = BitVec.ofNat 64 (2 * xl.toNat)
  r1 : S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat + 4)
  sp : S.regs 4 = s.regs 4 - 176#64
  g : S.regs 14 = s.regs 14
  bp : S.regs 5 = s.regs 4 - 8#64
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  x15 : S.xmm 15 = s.xmm 15
  mret : S.mem.readLE ((s.regs 4).toNat - 176) 8 = 0x5f1106
  mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  m80 : S.mem.readLE ((s.regs 4).toNat - 80) 8 = 2 * xl.toNat
  m88 : S.mem.readLE ((s.regs 4).toNat - 88) 8 = 2 * xl.toNat + 4
  mst : S.mem.readLE ((s.regs 4).toNat + 32) 8 = st.toNat
  mxp : S.mem.readLE ((s.regs 4).toNat + 40) 8 = xp.toNat
  mxl : S.mem.readLE ((s.regs 4).toNat + 48) 8 = xl.toNat
  mxc : S.mem.readLE ((s.regs 4).toNat + 56) 8 = xc.toNat
  F : MemFrame s.mem S.mem (win s W 64)
  reg : S.mem.regions = s.mem.regions

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem alloc_head (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0fe0)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ S : State, AA s S W st xp xl xc → ReachesRet (LibSqr.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) s Q := by
  obtain ⟨hce, hsw, -, -, -, hxlc, hxc40, hxl12, -, hxh, -, hzc40, hzl, -, -, -, -, -, -, -, -⟩ := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  obtain ⟨-, hx48⟩ := hxh (by omega)
  have hzl' : 0 < zc.toNat → zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 := fun h => (hzl h).2.2.2
  clear hzl hxh hsw
  have hxx := toInt_small (xl + xl) (by rw [BitVec.toNat_add]; omega)
  janus64_run [BitVec.msb_eq_decide, toInt_small zc (by omega), toInt_small xl (by omega), hxx]
    until [cA "runtime.makeslice"]
  all_goals
    refine hK _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?F, ?_⟩
    case F => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first
      | omega
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | fail "SHOW"

end FvModexp.Amd64.NatSqr
