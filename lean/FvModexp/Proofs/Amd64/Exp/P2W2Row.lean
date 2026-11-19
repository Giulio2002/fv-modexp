import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.Exp.StkArgR
import FvModexp.Proofs.Amd64.Exp.P2W2E
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row: `nat.expNNPowerOfTwoWindowSize2` (amd64) on the Run extraction (agent divmc s75; twin of Arm64/Exp/P2W2Row)

`correctness` = `P2W2.ens` (the `PreC` / `CPostR` form of `fullC`) with the PROVED closed Q-form callees of
`CalleeInstQ` (`(*stack).nat`, `nat.sqr`, `nat.mul`, `nat.trunc` on `nsQ`), callee window `kc = mulWX64 = 30792`,
moved to `Extracted.program.link impl` (`Ensures.full64`); window `[RSP - stk, RSP + 0x60)` with
`41984 ≤ stk ≤ 2^20 + 0x1d8`. Runtime premises: the live `growslice`, `memclrNoHeapPointers`, `memmove`, `makeslice`,
`newobject`, `gcWriteBarrier2` contracts. `y` is the stack argument (`RSP + 8 …`), `logM` is `R10`.
`Witness.nonvacuous`: `z = nil`, the stack `{w, 0, 4}`, `x = [3]`, `y = [5]`, `logM = 8` (`3^5 mod 2^8`), `natOne`
(header outside the extracted data, its word in the `OB` object), a 64 KiB stack region, window `stk = 41984`, the
shared witness runtime, one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2Row

open FvModexp.Amd64.CalleeInstQ

/-- **window-2 power-of-two** (amd64): `z.expNNPowerOfTwoWindowSize2(stk, x, y, logM)` returns `x^y mod 2^logM` for
odd `x`, `y > 0`, `2 ≤ logM ≤ 2^13` (`P2W2.PreC` / `NHyp.CPostR`), for every runtime meeting the live allocation /
copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41984 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x1d8)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program P2W2.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 lm]
      (fun s => NHyp.StkArg0 s yp yl yc ∧
        P2W2.PreC R b L stk (P2W2.costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧ P2W2.EX xp xl s)
      (fun s s' => NHyp.CPostR R b L stk 0x60 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
        (P2W2.costB (stLen s.mem st) yl lm) s s') :=
  Ensures.mono_ret (Ensures.full64 (hinv := by janus64_pre_setRet [FvModexp.Amd64.NHyp.StkArg0, FvModexp.Amd64.P2W2.PreC, FvModexp.stLen, FvModexp.Amd64.P2W2.EX, FvModexp.Amd64.NHyp.CPre, FvModexp.natVal, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.win, FvModexp.Amd64.ExpHyp.stWs, FvModexp.Amd64.NHyp.StkApart, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.stkWs, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]) hap (by simp [numIntRegs])
    (P2W2.ens hap sub nf2 nfP hgr hmc hmv hmk hno hwb (kc := mulWX64) (by decide)
      (sn hap hgr hmc hwb) (by decide) (by decide) (sq hap hgr hmc hmv hmk hwb _) (by decide) (Nat.le_refl _)
      (mu hap hgr hmc hmv hmk hwb _) (Nat.le_refl _) (Nat.le_refl _) (tr hap hmv hmk) (by decide) (by decide)
      b L stk (by omega) (by simp only [P2Pre.K, mulWX64]; omega) hk2 zp zl zc st xp xl xc yp yl yc lm hzp hxc))
    (fun _ h => ⟨h.1.toStkArg, h.2⟩) (fun _ _ _ _ h => h)

end FvModexp.Amd64.P2W2Row

namespace FvModexp.Amd64.P2W2Row.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
/-- `natOne`'s header (outside the extracted data) and its backing word -/
abbrev NA : Nat := 12050400
abbrev OP : Nat := OB + 0x800
/-- the stack region below `SP0` (the entry `RSP`) -/
abbrev WW : Nat := 0x10000
abbrev BW : Nat := 0x100000
abbrev KW : Nat := 41984
abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88

theorem nA_eq : natOneA = NA := by decide
theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : StackNat.wbA = wbAw := by decide

/-- `x = [3]`, `y = [5]` (passed at `SP0 + 8 …`), the stack header, `natOne = {OP, 1, 1}` with `OP[0] = 1`, the four
`math/big` thresholds; all other bytes 0 (the return address `RET` at `SP0` comes from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = OP then 1
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = SP0 + 9 then 0x02 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 1 else if a = SP0 + 24 then 1
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xE0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩, ⟨NA, 24, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP,
    BitVec.ofNat 64 1, BitVec.ofNat 64 1, BitVec.ofNat 64 8]

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 XP else if i = 8 then 1
      else if i = 9 then 1 else if i = 10 then 8 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program P2W2.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program P2W2.fn)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv BW [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem stLen0 : stLen mem0 ST = 0 := by decide +kernel

theorem bud : P2W2.costB 0 1 8 ≤ BW := by decide +kernel

theorem one0 : NatOne R [] s0.mem OP (win s0 KW 0x60 ++ [(0, 0 + 8 * 0)] ++ stWs s0.mem ST) := by
  have hm : s0.mem = mem0 := rfl
  dsimp only [NatOne]
  rw [nA_eq, hm]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel

theorem sg0 : StackGuardOK s0 KW :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel, by decide +kernel⟩

theorem tls0 : TlsG s0 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem rd0 (p n : Nat) (hp : (p, n) ∈ [(XP, 1), (YP, 1)]) :
    RdIn R [] s0 KW 0x60 p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s0.mem p n ∧ Apart p (8 * n) ST 24 ∧
      Apart p (8 * n) (NHyp.freeOf s0.mem ST).1 (NHyp.freeOf s0.mem ST).2 ∧ (0 < 0 → Apart 0 (8 * 0) p (8 * n)) := by
  have hm : s0.mem = mem0 := rfl
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨⟨by decide, by rw [hm, acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩, by decide, ?_, ?_, ?_,
      fun h => absurd h (by decide)⟩
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
    · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
    · simp only [NatNorm, hm]; decide +kernel
    · simp only [Apart]; decide
    · simp only [Apart, hm]; decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies window-2's precondition (`3^5 mod 2^8`, `z = nil`) at window `stk = 41984` -/
theorem pre : NHyp.StkArg s0 0 YP 1 1 ∧
    P2W2.PreC R BW [] KW (P2W2.costB (stLen s0.mem ST) 1 8) 0 0 0 ST XP 1 YP 1 8 s0 ∧ P2W2.EX XP 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  refine ⟨⟨by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel⟩,
    ⟨?_, by rw [hm]; decide +kernel, by rw [hm]; decide +kernel, by decide, by decide, by decide, ⟨OP, one0, ?_⟩⟩, ?_⟩
  · unfold NHyp.CPre CallEnv TlsOK
    repeat' (first
      | exact inv1 _
      | exact WStubs.serves []
      | exact roOut
      | exact sg0
      | exact tls0
      | exact rd0
      | exact dataLoaded _ _
      | (rw [hm, stLen0]; exact bud)
      | apply And.intro)
    all_goals try simp only [win, h4, h14, hfs, hm, stLen0]
    all_goals first
      | decide
      | (intro r hr; simp at hr; done)
      | (intro h; exact absurd h (by decide))
      | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [Apart, gA_eq, wbA_eq, nA_eq]; decide +kernel)
      | (rw [acc0]; decide +kernel)
      | (simp only [StkOK, NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, acc0]; decide +kernel)
      | decide +kernel
      | trivial
      | (simp only [List.map_nil, List.nil_append, List.append_nil, outside_nil]; done)
      | (show Outside _ _ (List.append [] []); trivial)
      | (intro _; simp only [outside_cons, outside_nil, and_true, Apart]; decide +kernel)
      | skip
  · intro _
    refine ⟨by simp only [Apart]; decide, fun _ => ?_⟩
    simp only [Apart, hm]; decide +kernel
  · simp only [P2W2.EX, hm, nA_eq, gA_eq, Apart]
    refine ⟨fun _ => by decide, by decide +kernel, by rw [acc0]; decide +kernel⟩

/-- `pre` with the stack arguments in the row (audit) form `StkArg0` -/
theorem pre0 : NHyp.StkArg0 s0 YP 1 1 ∧
    P2W2.PreC R BW [] KW (P2W2.costB (stLen s0.mem ST) 1 8) 0 0 0 ST XP 1 YP 1 8 s0 ∧ P2W2.EX XP 1 s0 :=
  ⟨NHyp.StkArg0.of_stkArg pre.1, pre.2⟩

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, window `stk = 41984`, the call `z.expNNPowerOfTwoWindowSize2(stk, 3, 5, 8)` with `z = nil`
and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk : Nat)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    41984 ≤ stk ∧ stk ≤ 2 ^ 20 + 0x1d8 ∧ zp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program P2W2.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 lm] s ∧
    (NHyp.StkArg0 s yp yl yc ∧
      P2W2.PreC R b L stk (P2W2.costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧ P2W2.EX xp xl s) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ NHyp.CPostR R b L stk 0x60 zp zc st (natVal (s.setRet ret).mem xp xl ^ natVal (s.setRet ret).mem yp yl % 2 ^ lm)
        (P2W2.costB (stLen (s.setRet ret).mem st) yl lm) (s.setRet ret) s' :=
  ⟨WStubs.impl, R, BW, [], KW, 0, 0, 0, ST, XP, 1, 1, YP, 1, 1, 8, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, Nat.le_refl _, by decide, by decide, by decide, hret,
    setup, pre0,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _) (by rw [WStubs.addr_no]; exact WStubs.no [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) BW [] KW (Nat.le_refl _) (by decide)
      0 0 0 ST XP 1 1 YP 1 1 8 (by decide) (by decide) s0 setup pre0 RET hret⟩

end FvModexp.Amd64.P2W2Row.Witness
