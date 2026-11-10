import FvModexp.Proofs.Lib.MontAmd64
import FvModexp.Proofs.Common.MaskWord
/-! PERF SCOUT (not library; `sorry`): one iteration of the `nat.montgomery` loop, amd64, assumed addMulVVWW ABI0 summary. -/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic

namespace ScoutX

def montFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery"
def amvFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0"
abbrev hasADX : Nat := 0xbb6b8a

abbrev AmvPre (s : State) : Prop :=
  (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 104 ≤ 2 ^ 48 ∧
  s.mem.accessible ((s.regs 4).toNat) 104 true = true ∧ s.mem.accessible hasADX 1 false = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) true = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = s.mem.readLE ((s.regs 4).toNat + 32) 8 ∨
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)) ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ((s.regs 4).toNat) 104

abbrev amvVal (s : State) : Nat :=
  s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 32) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) +
  s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 56) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) *
    s.mem.readLE ((s.regs 4).toNat + 80) 8 + s.mem.readLE ((s.regs 4).toNat + 88) 8

abbrev AmvQ (s : State) (m : Memory) : Prop :=
  m.readLE (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      amvVal s % 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  m.readLE ((s.regs 4).toNat + 96) 8 = amvVal s / 2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]

abbrev head : Nat := segAddr FvModexp.Lib.MontAmd64.program montFn + 0x202

theorem mask_lt (i cap : Nat) (h : i < cap) (hc : cap < 2 ^ 40) : True := trivial

set_option maxHeartbeats 4000000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 300 in
theorem iter (impl : List Amd64.Segment) (hamv : Summary0 (FvModexp.Lib.MontAmd64.program.link impl) (segAddr FvModexp.Lib.MontAmd64.program amvFn) AmvPre AmvQ)
    (ret : Nat) (hret : RetAddr (FvModexp.Lib.MontAmd64.program.link impl) ret) (Q : Amd64.Outcome → Prop)
    (S : State) (sp zp cap xp yp mp k n i c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 head) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 cap)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 yp)
    (h10 : S.regs 10 = BitVec.ofNat 64 (2 * n)) (h11 : S.regs 11 = BitVec.ofNat 64 i) (h12 : S.regs 12 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (fs : Nat) (hfs : S.fsBase.toNat = fs) (hfsb : 8 ≤ S.fsBase.toNat ∧ S.fsBase.toNat ≤ 2 ^ 48)
    (htr : M.accessible (S.fsBase.toNat - 8) 8 false = true) (htg : M.readLE (S.fsBase.toNat - 8) 8 = (S.regs 14).toNat)
    (hadx : M.accessible hasADX 1 false = true)
    (hal : sp % 8 = 0) (hsp48 : sp + 0x120 ≤ 2 ^ 48) (hsp0 : 0x80 ≤ sp) (hacc : M.accessible (sp - 0x80) 0x1a0 true = true)
    (hn : 0 < n) (hn2 : 2 * n ≤ cap) (hcap : cap < 2 ^ 40) (hi : i < n) (hc : c ≤ 1)
    (hzp : zp + 8 * cap ≤ 2 ^ 48) (hzacc : M.accessible zp (8 * cap) true = true)
    (hxacc : M.accessible xp (8 * n) false = true) (hmacc : M.accessible mp (8 * n) false = true)
    (hyacc : M.accessible yp (8 * n) false = true)
    (hxp : xp + 8 * n ≤ 2 ^ 48) (hyp : yp + 8 * n ≤ 2 ^ 48) (hmp : mp + 8 * n ≤ 2 ^ 48) (hk : k < 2 ^ 64)
    (hzs : Apart zp (8 * cap) (sp - 0x80) 0x1a0) (hzx : Apart zp (8 * cap) xp (8 * n)) (hzm : Apart zp (8 * cap) mp (8 * n))
    (hzy : Apart zp (8 * cap) yp (8 * n)) (htz : Apart (S.fsBase.toNat - 8) 8 zp (8 * cap)) (hts : Apart (S.fsBase.toNat - 8) 8 (sp - 0x80) 0x1a0)
    (r60 : M.readLE (sp + 0x60) 8 = 2 * n) (r68 : M.readLE (sp + 0x68) 8 = cap) (ra0 : M.readLE (sp + 0xa0) 8 = zp)
    (rc0 : M.readLE (sp + 0xc0) 8 = mp) (rc8 : M.readLE (sp + 0xc8) 8 = n) (rd0 : M.readLE (sp + 0xd0) 8 = n)
    (rd8 : M.readLE (sp + 0xd8) 8 = k) (re0 : M.readLE (sp + 0xe0) 8 = n) (r100 : M.readLE (sp + 0x100) 8 = xp)
    (r108 : M.readLE (sp + 0x108) 8 = n) (r110 : M.readLE (sp + 0x110) 8 = n) (r118 : M.readLE (sp + 0x118) 8 = yp) :
    Reaches ((FvModexp.Lib.MontAmd64.program.link impl).withExit ret) S Q := by
  set_option janus.omega.log 300 in
  janus64_run [FvModexp.mask_neg_sub_lt (i * 8) i cap (by omega) (by omega) (by omega), r60, r68, ra0, rc0, rc8, rd0, rd8, re0, r100, r108, r110, r118] until [head] calls [hamv]
  all_goals sorry

end ScoutX
