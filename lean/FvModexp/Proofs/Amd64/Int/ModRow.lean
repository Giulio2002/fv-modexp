import FvModexp.Proofs.Amd64.Int.ModCA
import FvModexp.Proofs.Amd64.NatQ.DivMC
import FvModexp.Proofs.Amd64.NatQ.ModBudQ
import FvModexp.Proofs.Amd64.Witness.StubsGrow
import FvModexp.Proofs.Amd64.Int.ModRowW
import FvModexp.Proofs.Amd64.Witness.Stubs
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# Row: `(*Int).Mod` (amd64) on the Run extraction — `z.Mod(z, y)` as `Run` calls it

Twin of Arm64/Int/ModRow.lean. `correctness` = `IMod.ensCA` moved to `Extracted.program.link impl` (`Ensures.full64`),
window `41800` below / `16` above `RSP`. Statement: `IMod.ModSpecA`'s pre/post (= `RunIface.ModSpec`'s, plus the
`hasADX` byte readable; coordinator DECISION on "[divmc s56]"): `IntPre`/`IntPost` with budget
`ModBudget (max (len z) (len y))`. Runtime premises: the live `makeslice`, `memmove` (+ `MemmoveZeroLive64`),
`newobject`, `gcWriteBarrier4`, `sync.(*Pool).Get`/`Put` (`*big.stack`, `StkSh`) contracts.

`nat.div` (as `QuoRem` calls it: `stk == nil`) is top's closed `Q.NatDiv.ensMC` (Amd64/NatQ/DivMC), its cost bound
`Q.BudM.bud` (Amd64/NatQ/ModBudQ); further runtime premises: `growslice`, `memclrNoHeapPointers`, `gcWriteBarrier2`.
`Witness.nonvacuous`: every hypothesis and every precondition conjunct hold together (the shared witness runtime
`WStubs.impl`, toy allocator, budget `0x80000`, a 64 KiB stack, the threshold globals at their initial values, the
`hasADX` byte, the call `z.Mod(z, y)` with `z = 7`, `y = 3`, one limb each; one call-site state per contract) and the
call returns.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe maxW ModBudget lenW PoolG ModX)

namespace FvModexp.Amd64.ModRow

/-- `(*Int).Mod`'s symbol -/
abbrev fnModL : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod"

theorem fn_eq : RunIface.P ++ "(*Int).Mod" = fnModL := by decide

/-- the precondition (`IMod.ModSpecA`'s, window 41800 / 16) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64) (s : State) :
    Prop :=
  S = StkSh ∧ (IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L 41800 16 [z.toNat, y.toNat] s ∧
    0 < IntV s.mem y.toNat ∧ IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧
    PoolG R s.mem (win s 41800 16) ∧ ModX s.mem z.toNat) ∧ s.mem.accessible Callees.adxAddr 1 false = true

/-- the postcondition: `RAX = z`, `z = z mod y` (`IntPost`), `y` unchanged, `fsBase` and `DF` kept -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
    IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L 41800 16 z.toNat
      (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧ IntV s'.mem y.toNat = IntV s.mem y.toNat

theorem modpre_setRet_pp (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < s.mem.readLE (z.toNat + 24) 8) (hg1 : 0 < s.mem.readLE (y.toNat + 24) 8)
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  simp only [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, List.forall_mem_cons, List.forall_mem_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, true_and, forall_eq, List.mem_singleton, forall_eq_or_imp, false_implies, implies_true, forall_const, List.Pairwise.nil] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntV, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.ModX, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Exp.B, FvModexp.Amd64.RunIface.IntOK, FvModexp.natVal, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.TlsOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem modpre_setRet_pn (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < s.mem.readLE (z.toNat + 24) 8) (hg1 : ¬ 0 < s.mem.readLE (y.toNat + 24) 8)
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  simp only [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, List.forall_mem_cons, List.forall_mem_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, true_and, forall_eq, List.mem_singleton, forall_eq_or_imp, false_implies, implies_true, forall_const, List.Pairwise.nil] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntV, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.ModX, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Exp.B, FvModexp.Amd64.RunIface.IntOK, FvModexp.natVal, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.TlsOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem modpre_setRet_p (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < s.mem.readLE (z.toNat + 24) 8)
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  by_cases hg1 : 0 < s.mem.readLE (y.toNat + 24) 8
  · exact modpre_setRet_pp R b L S z y  s ret hs hret hg0 hg1 hp
  · exact modpre_setRet_pn R b L S z y  s ret hs hret hg0 hg1 hp

theorem modpre_setRet_np (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ¬ 0 < s.mem.readLE (z.toNat + 24) 8) (hg1 : 0 < s.mem.readLE (y.toNat + 24) 8)
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  simp only [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, List.forall_mem_cons, List.forall_mem_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, true_and, forall_eq, List.mem_singleton, forall_eq_or_imp, false_implies, implies_true, forall_const, List.Pairwise.nil] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntV, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.ModX, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Exp.B, FvModexp.Amd64.RunIface.IntOK, FvModexp.natVal, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.TlsOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem modpre_setRet_nn (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ¬ 0 < s.mem.readLE (z.toNat + 24) 8) (hg1 : ¬ 0 < s.mem.readLE (y.toNat + 24) 8)
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  simp only [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, List.forall_mem_cons, List.forall_mem_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, true_and, forall_eq, List.mem_singleton, forall_eq_or_imp, false_implies, implies_true, forall_const, List.Pairwise.nil] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ModRow.Pre, FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntV, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.ModX, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Exp.B, FvModexp.Amd64.RunIface.IntOK, FvModexp.natVal, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.TlsOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, false_implies, true_implies]

theorem modpre_setRet_n (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ¬ 0 < s.mem.readLE (z.toNat + 24) 8)
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  by_cases hg1 : 0 < s.mem.readLE (y.toNat + 24) 8
  · exact modpre_setRet_np R b L S z y  s ret hs hret hg0 hg1 hp
  · exact modpre_setRet_nn R b L S z y  s ret hs hret hg0 hg1 hp

theorem modpre_setRet (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) 
    (hp : Pre R b L S z y s) :
    Pre R b L S z y (s.setRet ret) := by
  by_cases hg0 : 0 < s.mem.readLE (z.toNat + 24) 8
  · exact modpre_setRet_p R b L S z y  s ret hs hret  hg0 hp
  · exact modpre_setRet_n R b L S z y  s ret hs hret  hg0 hp

/-- `Pre` survives writing the return address (the `hinv` of `correctness` and of the `Ensures.full64` it applies). As `IMod.qrpre_setRet`: the list
quantifier of `IntPre` is expanded and the guards `0 < cap z` / `0 < cap y` are case-split, one declaration per case (`modpre_setRet_<z><y>`). -/
theorem modpre_inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (S : PoolShape) (z y : BitVec 64) (p : Janus.Amd64.Program) (entry : Nat)
    (args : List W64) : Ensures.SetRetInv p entry args (fun s => Pre R b L S z y s) :=
  fun s ret hs hret hp => modpre_setRet R b L S z y s ret hs hret hp

/-- **`(*Int).Mod`** (amd64): `z.Mod(z, y)` (`y > 0`, operands of at most 128 words) returns `z` holding `z mod y`,
leaves `y` unchanged, writes only `z`, the runtime's memory and the window; for every runtime meeting the live
contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb4 : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
      4096 R 4)
    (S : PoolShape)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R Free.stkT S)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R Free.stkT S)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program fnModL) [z, z, y]
      (Pre R b L S z y) (Post R b L z y) := by
  refine Ensures.of_old (modpre_inv R b L S z y _ _ _) ?_
  intro ret hret s hs ⟨hS, hp⟩
  subst hS
  have h := Ensures.full64 (hinv := fun s ret hs hret hq => (modpre_inv R b L StkSh z y _ _ _ s ret hs hret ⟨rfl, hq⟩).2) hap (by simp [numIntRegs])
    (IMod.mod_ensD impl hap R (Q.NatDiv.ensMC impl hap R hgr hmc hwb hmk hmv hmz hno hget hput) IMod.libDiv_sub
      IMod.libDiv_noQ
      (WbLiveContract64.of_codeIn (by rw [LibQR.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibQR.names) hwb4)
      (stk := 41800) (above := 16) (by omega) (by omega) (by decide) (by decide) Q.BudM.bud b L z y)
  rw [fn_eq] at h
  exact h.toOld ret hret s hs hp

end FvModexp.Amd64.ModRow

namespace FvModexp.Amd64.ModRow.Witness

open FvModexp.Amd64.AsmWit FvModexp.Amd64.ModRowW Janus.Contracts.Toy

set_option maxRecDepth 100000

abbrev gAw : Nat := 0xb4ae88
abbrev wbAw : Nat := 0xbb7040
abbrev adxW : Nat := 0xbb6b88
/-- the stack region below `SP0` -/
abbrev WW : Nat := 0x10000

theorem gA_eq : RunIface.gA = gAw := by decide
theorem wbA_eq : RunIface.wbA = wbAw := by decide
theorem adx_eq : Callees.adxAddr = adxW + 2 := by decide

/-- `z` header at `OA` (`abs = (OB, 1, 1)`, `7`), `y` at `OA + 0x40` (`abs = (OB + 0x40, 1, 1)`, `3`), the four
thresholds `40, 40, 12, 80` at `gA`; all other witness bytes 0 -/
def g (a : Nat) : Byte :=
  if a = OA + 10 then 0xE0 else if a = OA + 16 then 1 else if a = OA + 24 then 1 else
  if a = OA + 0x48 then 0x40 else if a = OA + 0x4A then 0xE0 else if a = OA + 0x50 then 1 else
  if a = OA + 0x58 then 1 else if a = OB then 7 else if a = OB + 0x40 then 3 else
  if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

/-- a 64 KiB stack, the other standard regions, the thresholds, `runtime.writeBarrier`'s flag word, `hasADX` -/
def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) := [BitVec.ofNat 64 OA, BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40)]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then BitVec.ofNat 64 OA
      else if i = 1 then BitVec.ofNat 64 (OA + 0x40)
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program fnModL), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup0 (segAddr Extracted.program fnModL)
    args s0 :=
  ⟨rfl, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x80000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem rtOut (a n : Nat) (h : WBUF + 64 ≤ a ∧ a + n ≤ HEAP) : Outside a n R.rt := by
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; simp only [BUMP, HEAP, WBUF] at *; omega

set_option maxHeartbeats 64000000 in
theorem pre : Pre R 0x80000 [] StkSh (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) s0 := by
  unfold Pre
  refine ⟨rfl, ?_⟩
  have hm : s0.mem = mem0 := rfl
  have hsp : s0.regs 4 = BitVec.ofNat 64 SP0 := rfl
  have hg : s0.regs 14 = BitVec.ofNat 64 G0 := rfl
  have hfs : s0.fsBase = BitVec.ofNat 64 (T0 + 8) := rfl
  simp only [IntPre, CallEnv, RunIface.Globals, PoolG, ModX, RunIface.IntOK, List.forall_mem_cons,
    List.pairwise_cons, List.mem_singleton, List.not_mem_nil, forall_eq, hm, hsp, hg, hfs]
  and_intros
  all_goals first
    | exact dataLoaded _ _
    | exact roOut
    | exact WStubs.serves []
    | exact inv1 _
    | (intro r hr; simp at hr; done)
    | (intros; trivial)
    | (simp only [List.nil_append, List.map_nil, List.append_nil, outside_nil]; done)
    | (show _ = _; decide)
    | (exact Or.inr (rtOut _ _ (by decide +kernel)))
    | (unfold NatLive; intro _; exact ⟨by decide +kernel, Or.inr (rtOut _ _ (by decide +kernel)),
        by simp only [acc0]; decide +kernel, by decide +kernel⟩)
    | (unfold NatNorm; right; decide +kernel)
    | (unfold IntLenLe maxW; decide +kernel)
    | (unfold Apart; decide +kernel)
    | (intro _; unfold Apart; decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [win, outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (simp only [acc0]; decide +kernel)
    | (constructor <;> first | decide +kernel | (rw [hm, acc0]; decide +kernel))
    | decide +kernel

theorem hty : TysOK [] := by intro t ht; simp at ht

/-- Every hypothesis of `correctness` holds, with every conjunct of its precondition, a call-site state per runtime
contract, and the returning run: the shared witness runtime, budget `0x80000`, empty live set, `z.Mod(z, y)` with
`z = 7`, `y = 3`. -/
theorem nonvacuous :
    ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64)
      (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R Free.stkT StkSh ∧
    Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R Free.stkT StkSh ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program fnModL) [z, z, y] s ∧
    Pre R b L StkSh z y s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier4") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧ Post R b L z y (s.setRet ret) s' :=
  ⟨WStubs.impl, R, 0x80000, [], BitVec.ofNat 64 OA, BitVec.ofNat 64 (OA + 0x40), RET, s0, WStubs.hap,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] hty _,
    by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _,
    by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _,
    hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb4A 0 0 0, by rw [WStubs.addr_wb4]; rfl, by rw [WStubs.addr_wb4]; exact site_wb _ _⟩,
    ⟨[], 0x1000, callS WStubs.getA OA 0 0, by rw [WStubs.addr_get]; rfl, by rw [WStubs.addr_get]; exact site_get _⟩,
    ⟨[(HEAP, HEAP + 24)], 0x1000, [(HEAP, HEAP + 24)], callP WStubs.putA, by rw [WStubs.addr_put]; rfl,
      by rw [WStubs.addr_put]; exact site_put _⟩,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _)
      (by rw [WStubs.addr_mv]; exact WStubs.mv R) (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_no]; exact WStubs.no [] hty _) (by rw [WStubs.addr_wb4]; exact WStubs.wb4 [] hty _) StkSh
      (by rw [WStubs.addr_get]; exact WStubs.get [] _ _ _) (by rw [WStubs.addr_put]; exact WStubs.put [] hty _ _ _)
      (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _) (by rw [WStubs.addr_cl]; exact WStubs.cl R)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) 0x80000 [] (BitVec.ofNat 64 OA) (BitVec.ofNat 64 (OA + 0x40)) s0 setup pre RET hret⟩

end FvModexp.Amd64.ModRow.Witness
