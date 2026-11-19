import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.Exp.P2Pre
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row: `buildPrecomputationWindowModPower2` (amd64) on the Run extraction (agent divmc s83)

`correctness` = `P2Pre.ens` with the PROVED closed Q-form callees of `CalleeInstQ` (`(*stack).nat`, `nat.sqr`, `nat.mul`,
`nat.trunc` on `nsQ`), callee window `kc = mulWX64 = 30792` (as in `P2W2Row` / `P2W4Row`), moved to
`Extracted.program.link impl` (`Ensures.full64`). Runtime premises: the live `growslice`, `memclrNoHeapPointers`,
`memmove`, `makeslice`, `newobject`, `gcWriteBarrier2` contracts. A release row of its own, run right before
`amd64 Exp/P2W2Row`, so the shared table-building closure (P2Pre*, CalleeInstQ, ~420 module-s) is compiled and replayed
by this row instead of by window-2 (docs/history/PERF-log.md "divmc s83").
`Witness.nonvacuous`: the stack `{w, 0, 4}`, `powers` = 4 nil headers, `windowSize = 2`, `logM = 8`, `x = [3]`,
`natOne` (header outside the extracted data, its word in the `OB` object), a 64 KiB stack region, the shared witness
runtime, one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2PreRow

open FvModexp.Amd64.CalleeInstQ

/-- `Scr` (a `structure`, which the Janus audit does not accept in a row statement) as the plain conjunction of its
fields -/
@[reducible] def ScrF (R : RtInv) (L L1 : List (Nat × Nat)) (m0 m : Memory) (st t k : Nat) : Prop :=
  t + 8 * k ≤ 2 ^ 48 ∧ m.accessible t (8 * k) true = true ∧ t % 8 = 0 ∧ Held R L1 t (8 * k) ∧
    ((0 < stCap m0 st ∧ stW m0 st + 8 * stLen m0 st ≤ t ∧ t + 8 * k ≤ stW m0 st + 8 * stCap m0 st) ∨
      (InRanges t (8 * k) R.rt ∧ ApartAll t (8 * k) L))

/-- `P2Pre.Post` with `Scr` spelled out (`ScrF`); otherwise word for word -/
@[reducible] def PostR (R : RtInv) (kc : Nat) (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ bp : Nat, (∀ j, j < pl → P2Pre.PwD s'.mem pw bp lm (natVal s.mem x xl) j) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧
      b - P2Pre.cost pl lm + stkR (P2Pre.HP (stLen s.mem st) pl lm) s'.mem st ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      ScrF R L L' s.mem s'.mem st bp (P2Pre.NB pl lm) ∧ Q.NatSqr.StkSep s'.mem st bp (8 * P2Pre.NB pl lm) ∧
      P2Pre.StkAfter R L L' st (stLen s.mem st) pl lm s.mem s'.mem ∧
      MemFrame s.mem s'.mem (P2Pre.AW R kc s pw pl st) ∧ LiveFrame s.mem s'.mem L (P2Pre.LW s pw pl st) ∧
      ArrIn L' st s.mem s'.mem ∧ P2Pre.BU s'.mem st bp (8 * P2Pre.NB pl lm)

theorem postR_of {R : RtInv} {kc b : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s s' : State}
    (h : P2Pre.Post R kc b L st pw pl lm x xl s s') : PostR R kc b L st pw pl lm x xl s s' := by
  obtain ⟨h1, h2, bp, hpw, L', b', hx, hb, hinv, hscr, rest⟩ := h
  exact ⟨h1, h2, bp, hpw, L', b', hx, hb, hinv, ⟨hscr.b48, hscr.acc, hscr.al, hscr.held, hscr.loc⟩, rest⟩

/-- **`buildPrecomputationWindowModPower2`** (amd64): `buildPrecomputationWindowModPower2(stk, powers, windowSize, logM,
x)` with `windowSize ∈ {2, 4}`, `len powers = 2^windowSize`, `2 ≤ logM ≤ 2^13`, `x` normalised stores
`powers[j] = x^j mod 2^logM` (`P2Pre.Post`, as `PostR`), for every runtime meeting the live allocation / copy / clear /
write-barrier contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl pc ws lm x xl xc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program P2Pre.fn)
      [BitVec.ofNat 64 st, BitVec.ofNat 64 pw, BitVec.ofNat 64 pl, BitVec.ofNat 64 pc, BitVec.ofNat 64 ws,
        BitVec.ofNat 64 lm, BitVec.ofNat 64 x, BitVec.ofNat 64 xl, BitVec.ofNat 64 xc]
      (P2Pre.PreE R mulWX64 b L st pw pl ws lm x xl) (PostR R mulWX64 b L st pw pl lm x xl) :=
  Ensures.mono_ret (Ensures.full64 (hinv := P2Pre.preE_inv _ _ _) hap (by simp [numIntRegs])
    (P2Pre.ens hap sub nfP hmv hwb (kc := mulWX64) (by decide) (sn hap hgr hmc hwb) (by decide) (by decide)
      (sq hap hgr hmc hmv hmk hwb _) (by decide) (Nat.le_refl _) (mu hap hgr hmc hmv hmk hwb _) (Nat.le_refl _)
      (Nat.le_refl _) (tr hap hmv hmk) (by decide) (by decide) b L st pw pl pc ws lm x xl xc))
    (fun _ h => h) (fun _ _ _ _ h => postR_of h)

end FvModexp.Amd64.P2PreRow

namespace FvModexp.Amd64.P2PreRow.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `powers`: four nil slice headers -/
abbrev PW : Nat := OA + 0x400
abbrev XP : Nat := OB + 0x100
/-- `natOne`'s header (outside the extracted data) and its backing word -/
abbrev NA : Nat := 12050400
abbrev OP : Nat := OB + 0x800
/-- the stack region below `SP0` (the entry `RSP`) -/
abbrev WW : Nat := 0x10000
abbrev BW : Nat := 0x100000
abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88

theorem nA_eq : natOneA = NA := by decide
theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : StackNat.wbA = wbAw := by decide

/-- `x = [3]`, the stack header, `natOne = {OP, 1, 1}` with `OP[0] = 1`, the four `math/big` thresholds; all other
bytes 0 (the return address `RET` at `SP0` comes from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = OP then 1
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xE0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩, ⟨NA, 24, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 ST, BitVec.ofNat 64 PW, BitVec.ofNat 64 4, BitVec.ofNat 64 4, BitVec.ofNat 64 2,
    BitVec.ofNat 64 8, BitVec.ofNat 64 XP, BitVec.ofNat 64 1, BitVec.ofNat 64 1]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 ST else if i = 3 then BitVec.ofNat 64 PW else if i = 1 then 4
      else if i = 7 then 4 else if i = 6 then 2 else if i = 8 then 8 else if i = 9 then BitVec.ofNat 64 XP
      else if i = 10 then 1 else if i = 11 then 1 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program P2Pre.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program P2Pre.fn)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem invB (bb gp : Nat) (hb : HEAP + 64 * bb ≤ HEND) : R.inv bb [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) hb (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem stLen0 : stLen mem0 ST = 0 := by decide +kernel

theorem inv1 (gp : Nat) : R.inv (BW + stkR (P2Pre.HP (stLen mem0 ST) 4 8) mem0 ST) [] gp (view R.rt [] mem0) :=
  invB _ gp (by rw [stLen0]; decide +kernel)

theorem one0 : NatOne R [] mem0 OP (win s0 (P2Pre.K mulWX64) P2Pre.A ++ P2Pre.LW s0 PW 4 ST) := by
  dsimp only [NatOne]
  rw [nA_eq]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, P2Pre.LW, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, P2Pre.LW, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel

theorem sg0 : StackGuardOK s0 (P2Pre.K mulWX64) :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel, by decide +kernel⟩

theorem tls0 : TlsG s0 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem rd0 : RdIn R [] s0 (P2Pre.K mulWX64) P2Pre.A XP 1 := by
  have hm : s0.mem = mem0 := rfl
  refine ⟨by decide, by rw [hm, acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`windowSize = 2`, `logM = 8`, `x = [3]`) -/
theorem pre : P2Pre.PreE R mulWX64 BW [] ST PW 4 2 8 XP 1 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  unfold P2Pre.PreE CallEnv TlsOK
  repeat' (first
    | exact inv1 _
    | exact WStubs.serves []
    | exact roOut
    | exact sg0
    | exact tls0
    | exact rd0
    | exact dataLoaded _ _
    | apply And.intro)
  all_goals try simp only [win, h4, h14, hfs, hm, stLen0]
  all_goals first
    | decide
    | exact ⟨OP, one0, by simp only [Q.NatSqr.StkSep, Apart, gA_eq]; decide +kernel⟩
    | (simp only [NatNorm]; decide +kernel)
    | (intro r hr; simp at hr; done)
    | (intro h; exact absurd h (by decide))
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart, gA_eq, wbA_eq]; decide +kernel)
    | (rw [acc0]; decide +kernel)
    | (simp only [NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, acc0]; decide +kernel)
    | decide +kernel
    | trivial
    | (intro _; simp only [outside_cons, outside_nil, and_true, Apart]; decide +kernel)
    | (intro _; simp only [Q.NatSqr.StkSep, Apart, gA_eq]; decide +kernel)

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, empty live set, the call `buildPrecomputationWindowModPower2(stk, powers, 2, 8, [3])` with the stack
`{w, 0, 4}` and `powers` = four nil headers; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (st pw pl pc ws lm x xl xc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program P2Pre.fn)
      [BitVec.ofNat 64 st, BitVec.ofNat 64 pw, BitVec.ofNat 64 pl, BitVec.ofNat 64 pc, BitVec.ofNat 64 ws,
        BitVec.ofNat 64 lm, BitVec.ofNat 64 x, BitVec.ofNat 64 xl, BitVec.ofNat 64 xc] s ∧
    P2Pre.PreE R mulWX64 b L st pw pl ws lm x xl s ∧
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
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧ PostR R mulWX64 b L st pw pl lm x xl (s.setRet ret) s' :=
  ⟨WStubs.impl, R, BW, [], ST, PW, 4, 4, 2, 8, XP, 1, 1, RET, s0, WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, hret, setup, pre,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) BW [] ST PW 4 4 2 8 XP 1 1 s0 setup pre RET hret⟩

end FvModexp.Amd64.P2PreRow.Witness
