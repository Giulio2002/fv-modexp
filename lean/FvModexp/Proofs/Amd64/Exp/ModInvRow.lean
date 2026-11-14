import FvModexp.Proofs.Amd64.Exp.ModInv
import FvModexp.Proofs.Amd64.Exp.CalleeInstE
import FvModexp.Proofs.Amd64.Exp.P2DRow
import FvModexp.Proofs.Amd64.Nat.RowLink

set_option autoImplicit false

/-!
# Row: `nat.modularInverseModPowerOfTwo` (amd64) on the Run extraction (agent asm s80; twin of infra's
Arm64/Exp/ModInvRow)

`correctness` = infra's amd64 `ModInv.ens` (Q-form `PreQ` / `PostQ`: one reserve level `H`, cost
`ModInv.cost sqrCQ mulCQ xl n + stkR H s.mem st`) with the PROVED callees of `CalleeInstQ` / `CalleeInstE` exactly as
`nat.expNNEven` instantiates it (`ExpEven.miEQ`): divmc's Q-form `nat.sqr` / `nat.mul` (window `mulWX64`), asm's
`nat.trunc` / `nat.lsh`, `nat.sub` (`ensR0`), `nat.add` (`ensR`), `nat.subMod2N` (inside `ModInv.ens`); callee frame
`kc = mulWX64`; moved to `Extracted.program.link impl` (`Ensures.full64`). All eight arguments are in registers
(`RAX RBX RCX RDI RSI R8 R9 R10`): the precondition reads no stack word. Runtime premises: the live `growslice`,
`memclrNoHeapPointers`, `memmove`, `makeslice`, `gcWriteBarrier2` contracts.
A LOWER row of `amd64 Exp/EvenRow` (its `modInv` closure is compiled and replayed here).
`Witness.nonvacuous`: `x = [3]`, `n = 64` (the `n ≤ 64` path, nat.go:1300), `z` an all-zero 2-word array, the stack
`{w, 0, 4}`, `natOne`, reserve level `H = D 64 = 80`; one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInvRow

open FvModexp.Amd64.CalleeInstQ

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.modularInverseModPowerOfTwo`** (amd64): `z.modularInverseModPowerOfTwo(stk, x, n)` returns a normalised nat
holding the inverse of odd `x` modulo `2^n` (`Exp.modularInverseModPowerOfTwo`), in `z`'s array or a fresh one
(`ModInv.PreQ` / `PostQ` at callee frame `mulWX64`, costs `sqrCQ` / `mulCQ`), for every runtime meeting the live
allocation / copy / clear / write-barrier contracts. -/
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
    (H B : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ModInv.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n]
      (ModInv.PreQ R mulWX64 H sqrCQ mulCQ B L zp zl zc st xp xl xc n)
      (ModInv.PostQ R mulWX64 H sqrCQ mulCQ B L zp zc st xp xl n) :=
  Ensures.full64 hap (by simp [numIntRegs])
    (ModInv.ens hap sub sub sub sub nfM nfM nfM nfM nfS hmk (by decide) (sq hap hgr hmc hmv hmk hwb mulWX64)
      (Nat.le_refl _) (by decide) (tr hap hmv hmk) (by decide) (by decide) (mu hap hgr hmc hmv hmk hwb mulWX64)
      (Nat.le_refl _) (Nat.le_refl _) (lh hap hmc hmv hmk) (by decide) (by decide) (sb hap hmv hmk) (ad hap hmv hmk)
      hgr (fun _ _ h => sqrCQ_mono h) (fun _ _ h => sqrCQ_mono h) (fun _ _ _ h => mulCQ_mono h (Nat.le_refl _))
      H B L zp zl zc st xp xl xc n)

end FvModexp.Amd64.ModInvRow

namespace FvModexp.Amd64.ModInvRow.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp
open FvModexp.Amd64.P2DRow.Witness (NA OP WW BW gAw wbAw adxW nA_eq gA_eq wbA_eq hret hty)

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
/-- `z`'s (all-zero, 2-word) array -/
abbrev ZP : Nat := OA + 0x400
abbrev XP : Nat := OB + 0x100
/-- the window below `RSP`: `ModInv.K mulWX64 = 232 + 30792` -/
abbrev KW : Nat := 31024
abbrev HW : Nat := 80

/-- `x = [3]`, the stack header, `natOne = {OP, 1, 1}` with `OP[0] = 1`, the four `math/big` thresholds; all other
bytes 0 (the return address `RET` at `SP0` from `toyBytes`) -/
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
  [BitVec.ofNat 64 ZP, BitVec.ofNat 64 0, BitVec.ofNat 64 2, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP,
    BitVec.ofNat 64 1, BitVec.ofNat 64 1, BitVec.ofNat 64 64]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 ZP else if i = 1 then 2
      else if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 XP else if i = 8 then 1
      else if i = 9 then 1 else if i = 10 then 64 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program ModInv.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program ModInv.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
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

theorem bud : ModInv.cost sqrCQ mulCQ 1 64 + stkR HW mem0 ST ≤ BW := by decide +kernel

theorem one0 : NatOne R [] s0.mem OP (win s0 KW ModInv.A) := by
  have hm : s0.mem = mem0 := rfl
  dsimp only [NatOne]
  rw [nA_eq, hm]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [win, outside_cons, outside_nil, and_true]; decide +kernel

theorem sg0 : StackGuardOK s0 KW :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem tls0 : TlsG s0 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies `PreQ` (`x = 3`, `n = 64`, `z` a 2-word array) at `H = 80` (`= 0 + D 64`) -/
theorem pre : ModInv.PreQ R mulWX64 HW sqrCQ mulCQ BW [] ZP 0 2 ST XP 1 1 64 s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  have hK : ModInv.K mulWX64 = KW := by decide
  have hcb : ModInv.cost sqrCQ mulCQ 1 64 + stkR HW s0.mem ST ≤ BW := by rw [hm]; exact bud
  unfold ModInv.PreQ ModInv.OneIn
  rw [hK]
  refine ⟨?_, WStubs.serves [], ⟨?_, ?_⟩, by decide, by decide, by decide, by decide, by decide, ?_, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_, ⟨?_, by decide⟩, ?_, ?_, ?_, ?_, ?_, ⟨?_, hcb⟩, inv1 _, ?_, ?_,
    ⟨OP, one0, ?_, ?_, ?_, ?_⟩⟩
  all_goals try unfold CallEnv TlsOK
  all_goals try simp only [Q.NatSqr.StkPre, Q.NatSqr.StkSep, RunIface.Globals, WrOut, RdIn]
  repeat' (first
    | exact sg0
    | exact tls0
    | exact dataLoaded _ _
    | exact roOut
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
    | (simp only [NatNorm]; decide +kernel)
    | (simp only [StkOK, NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, acc0]; decide +kernel)
    | (simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [BasicSqr.freeP, BasicSqr.freeN, stW, stLen, stCap, Apart, Held, InRanges, rt_eq, outside_cons,
        outside_nil, and_true]; decide +kernel)
    | (intro _; simp only [BasicSqr.freeP, BasicSqr.freeN, stW, stLen, stCap, Apart, outside_cons, outside_nil,
        and_true]; decide +kernel)
    | (simp only [Q.NatSqr.guard, Q.NatSqr.tls, Apart, BasicSqr.freeP, BasicSqr.freeN, stW, stLen, stCap];
        decide +kernel)
    | (intro _; simp only [Q.NatSqr.guard, Q.NatSqr.tls, Apart, stW, stCap]; decide +kernel)
    | (intro _; simp only [win, Apart, outside_cons, outside_nil, and_true, Q.NatSqr.guard, Q.NatSqr.tls, stW, stCap,
        h4, h14, hfs, hm]; decide +kernel)
    | decide +kernel
    | trivial

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `BW`, reserve level `H = 80`, empty live set, the call `z.modularInverseModPowerOfTwo(stk, 3, 64)` with a
2-word `z` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (H B : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc n : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program ModInv.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 n] s ∧
    ModInv.PreQ R mulWX64 H sqrCQ mulCQ B L zp zl zc st xp xl xc n s ∧
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
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ ModInv.PostQ R mulWX64 H sqrCQ mulCQ B L zp zc st xp xl n s s' :=
  ⟨WStubs.impl, R, HW, BW, [], ZP, 0, 2, ST, XP, 1, 1, 64, RET, s0, WStubs.hap,
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
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) HW BW [] ZP 0 2 ST XP 1 1 64 RET hret s0 setup pre⟩

end FvModexp.Amd64.ModInvRow.Witness
