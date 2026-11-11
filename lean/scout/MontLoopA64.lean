import FvModexp.Proofs.Lib.MontA64
/-! PERF SCOUT (not part of the library; contains `sorry`): one iteration of the `nat.montgomery` loop, arm64,
with an assumed `addMulVVWW.abi0` ABI0 summary. -/
open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec

namespace Scout

def montFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery"
def amvFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0"
def subFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.subVV.abi0"


/-- assumed shape of the addMulVVWW ABI0 precondition (frame words z,zl,zc,x,xl,xc,y,yl,yc,m,a; result word 11) -/
abbrev AmvPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 104 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat + 8) 96 true = true ∧
  s.mem.accessible (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) true = true ∧
  s.mem.accessible (s.mem.readLE (s.sp.toNat + 32) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) false = true ∧
  s.mem.accessible (s.mem.readLE (s.sp.toNat + 56) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) false = true ∧
  (s.mem.readLE (s.sp.toNat + 8) 8 = s.mem.readLE (s.sp.toNat + 32) 8 ∨
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8)
      (s.mem.readLE (s.sp.toNat + 32) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8)) ∧
  Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8)
      (s.mem.readLE (s.sp.toNat + 56) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) (s.sp.toNat + 96) 8

abbrev amvVal (s : State) : Nat :=
  s.mem.readLE (s.mem.readLE (s.sp.toNat + 32) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) +
  s.mem.readLE (s.mem.readLE (s.sp.toNat + 56) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) *
    s.mem.readLE (s.sp.toNat + 80) 8 + s.mem.readLE (s.sp.toNat + 88) 8

abbrev AmvQ (s : State) (m : Memory) : Prop :=
  m.readLE (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) =
      amvVal s % 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  m.readLE (s.sp.toNat + 96) 8 = amvVal s / 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 96, s.sp.toNat + 104)]

theorem mask_lt (i cap : Nat) (h : i < cap) (hc : cap < 2 ^ 63) :
    i &&& ((BitVec.ofNat 64 i - BitVec.ofNat 64 cap).sshiftRight 63).toNat = i := by
  have : (BitVec.ofNat 64 i - BitVec.ofNat 64 cap).sshiftRight 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight]
    sorry
  rw [this, BitVec.toNat_allOnes]
  sorry

abbrev head : Nat := segAddr FvModexp.Lib.MontA64.program montFn + 0x194

set_option maxHeartbeats 4000000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 300 in
theorem iter (impl : List Segment) (hamv : Summary0 (FvModexp.Lib.MontA64.program.link impl) (segAddr FvModexp.Lib.MontA64.program amvFn) AmvPre AmvQ)
    (ret : Nat) (hret : RetAddr (FvModexp.Lib.MontA64.program.link impl) ret) (Q : Outcome → Prop)
    (S : State) (sp zp cap xp yp mp k n i c : Nat) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 head) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 cap)
    (h3 : S.regs 3 = BitVec.ofNat 64 xp) (h4 : S.regs 4 = BitVec.ofNat 64 n) (h5 : S.regs 5 = BitVec.ofNat 64 n)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 i) (h8 : S.regs 8 = BitVec.ofNat 64 c)
    (h9 : S.regs 9 = BitVec.ofNat 64 mp) (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h12 : S.regs 12 = BitVec.ofNat 64 k) (h13 : S.regs 13 = BitVec.ofNat 64 n)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (hal : sp % 16 = 0) (hsp48 : sp + 320 ≤ 2 ^ 48) (hacc : M.accessible sp 320 true = true)
    (hn : 0 < n) (hn2 : 2 * n ≤ cap) (hcap : cap < 2 ^ 40) (hi : i < n) (hc : c ≤ 1)
    (hzp : zp + 8 * cap ≤ 2 ^ 48) (hzacc : M.accessible zp (8 * cap) true = true)
    (hxacc : M.accessible xp (8 * n) false = true) (hmacc : M.accessible mp (8 * n) false = true)
    (hyacc : M.accessible yp (8 * n) false = true)
    (hxp : xp + 8 * n ≤ 2 ^ 48) (hyp : yp + 8 * n ≤ 2 ^ 48) (hmp : mp + 8 * n ≤ 2 ^ 48) (hk : k < 2 ^ 64)
    (hzs : Apart zp (8 * cap) sp 320) (hzx : Apart zp (8 * cap) xp (8 * n)) (hzm : Apart zp (8 * cap) mp (8 * n))
    (hzy : Apart zp (8 * cap) yp (8 * n))
    (r104 : M.readLE (sp + 104) 8 = 2 * n) (r112 : M.readLE (sp + 112) 8 = cap) (r168 : M.readLE (sp + 168) 8 = zp)
    (r224 : M.readLE (sp + 224) 8 = xp) (r232 : M.readLE (sp + 232) 8 = n) (r240 : M.readLE (sp + 240) 8 = n)
    (r248 : M.readLE (sp + 248) 8 = yp) (r272 : M.readLE (sp + 272) 8 = mp) (r280 : M.readLE (sp + 280) 8 = n)
    (r288 : M.readLE (sp + 288) 8 = n) (r296 : M.readLE (sp + 296) 8 = k) (r304 : M.readLE (sp + 304) 8 = n) :
    Reaches ((FvModexp.Lib.MontA64.program.link impl).withExit ret) S Q := by
  set_option janus.omega.log 300 in
  janus_run [mask_lt i cap (by omega) (by omega), r104, r112, r168, r224, r232, r240, r248, r272, r280, r288, r296, r304] until [head] calls [hamv]
  all_goals sorry

end Scout
