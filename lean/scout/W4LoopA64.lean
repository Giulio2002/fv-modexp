import FvModexp.Proofs.Lib.W4A64
/-! PERF SCOUT (not library; `sorry`): the four squarings of the window-4 inner loop, arm64, assumed montgomery summary. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ScoutW
def w4Fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4"
def montFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery"
abbrev body : Nat := segAddr FvModexp.Lib.W4A64.program w4Fn + 0x8e8
abbrev stop : Nat := segAddr FvModexp.Lib.W4A64.program w4Fn + 0xa10

/-- assumed montgomery (roomy) precondition -/
abbrev MPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.sp.toNat % 16 = 0 ∧ 4096 ≤ s.sp.toNat ∧
  s.sp.toNat + 120 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 4096) (4096 + 120) true = true ∧
  (s.regs 4) = (s.regs 13) ∧ (s.regs 7) = (s.regs 13) ∧ (s.regs 10) = (s.regs 13) ∧
  2 * (s.regs 13).toNat ≤ (s.regs 2).toNat ∧ (s.regs 2).toNat < 2 ^ 40 ∧
  (s.regs 0).toNat + 8 * (s.regs 2).toNat ≤ 2 ^ 48 ∧
  s.mem.accessible (s.regs 0).toNat (8 * (s.regs 2).toNat) true = true ∧
  s.mem.accessible (s.regs 3).toNat (8 * (s.regs 13).toNat) false = true ∧
  s.mem.accessible (s.regs 6).toNat (8 * (s.regs 13).toNat) false = true ∧
  s.mem.accessible (s.regs 9).toNat (8 * (s.regs 13).toNat) false = true ∧
  Apart (s.regs 0).toNat (8 * (s.regs 2).toNat) (s.regs 3).toNat (8 * (s.regs 13).toNat) ∧
  Apart (s.regs 0).toNat (8 * (s.regs 2).toNat) (s.regs 6).toNat (8 * (s.regs 13).toNat) ∧
  Apart (s.regs 0).toNat (8 * (s.regs 2).toNat) (s.regs 9).toNat (8 * (s.regs 13).toNat) ∧
  Apart (s.regs 0).toNat (8 * (s.regs 2).toNat) (s.sp.toNat - 4096) (4096 + 120)

/-- assumed montgomery value (opaque here) -/
opaque montV : Nat → Nat → Nat → Nat → Nat → Nat

abbrev MPost (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [s.regs 0, s.regs 13, s.regs 2] f v m ex ep ∧
    m.readLE (s.regs 0).toNat (8 * (s.regs 13).toNat) =
      montV (s.regs 13).toNat (s.mem.readLE (s.regs 3).toNat (8 * (s.regs 13).toNat))
        (s.mem.readLE (s.regs 6).toNat (8 * (s.regs 13).toNat)) (s.mem.readLE (s.regs 9).toNat (8 * (s.regs 13).toNat))
        (s.regs 12).toNat ∧
    MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + 8 * (s.regs 2).toNat),
      (s.sp.toNat - 4096, s.sp.toNat + 120)]

set_option maxHeartbeats 4000000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 300 in
theorem iter (impl : List Segment)
    (hmont : Summary (FvModexp.Lib.W4A64.program.link impl) (segAddr FvModexp.Lib.W4A64.program montFn) MPre MPost)
    (ret : Nat) (hret : RetAddr (FvModexp.Lib.W4A64.program.link impl) ret) (Q : Outcome → Prop)
    (S : State) (sp ap acap bp bcap mp mcap k0 n yi kk : Nat) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 body) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 ap) (h13 : S.regs 13 = BitVec.ofNat 64 n) (h14 : S.regs 14 = BitVec.ofNat 64 acap)
    (h1 : S.regs 1 = BitVec.ofNat 64 bp) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h15 : S.regs 15 = BitVec.ofNat 64 bcap)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 mcap)
    (h12 : S.regs 12 = BitVec.ofNat 64 k0) (h20 : S.regs 20 = BitVec.ofNat 64 yi) (h21 : S.regs 21 = BitVec.ofNat 64 kk)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (hal : sp % 16 = 0) (hsp0 : 8192 ≤ sp) (hsp48 : sp + 1040 ≤ 2 ^ 48) (hacc : M.accessible (sp - 4096) (4096 + 1040) true = true)
    (hn : 0 < n) (hna : 2 * n ≤ acap) (hnb : 2 * n ≤ bcap) (hca : acap < 2 ^ 40) (hcb : bcap < 2 ^ 40) (hmc : n ≤ mcap)
    (hap : ap + 8 * acap ≤ 2 ^ 48) (hbp : bp + 8 * bcap ≤ 2 ^ 48) (hmp : mp + 8 * n ≤ 2 ^ 48) (hk0 : k0 < 2 ^ 64)
    (hyi : yi < 2 ^ 64) (hkk : kk < 2 ^ 64)
    (haacc : M.accessible ap (8 * acap) true = true) (hbacc : M.accessible bp (8 * bcap) true = true)
    (hmacc : M.accessible mp (8 * n) false = true)
    (hab : Apart ap (8 * acap) bp (8 * bcap)) (ham : Apart ap (8 * acap) mp (8 * n)) (hbm : Apart bp (8 * bcap) mp (8 * n))
    (has : Apart ap (8 * acap) (sp - 4096) (4096 + 1040)) (hbs : Apart bp (8 * bcap) (sp - 4096) (4096 + 1040))
    (hms : Apart mp (8 * n) (sp - 4096) (4096 + 1040))
    (r1016 : M.readLE (sp + 1016) 8 = mp) (r1024 : M.readLE (sp + 1024) 8 = n) (r1032 : M.readLE (sp + 1032) 8 = mcap)
    (r224 : M.readLE (sp + 224) 8 = k0) (r904 : M.readLE (sp + 904) 8 = bp) (r328 : M.readLE (sp + 328) 8 = n)
    (r320 : M.readLE (sp + 320) 8 = bcap) :
    Reaches ((FvModexp.Lib.W4A64.program.link impl).withExit ret) S Q := by
  set_option janus.omega.log 300 in
  janus_run [r1016, r1024, r1032, r224, r904, r328, r320] until [stop] calls [hmont]
  all_goals sorry
end ScoutW
