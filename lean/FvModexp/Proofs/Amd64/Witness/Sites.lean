import FvModexp.Proofs.Amd64.Witness.AsmWit
import Janus.Contracts.PoolAmd64

/-!
# More call-site states of the runtime contracts (amd64; Janus U-WITNESS-CALLSITE)

Companion of `AsmWit.site_mv`/`site_cl`/`site_mk` for the other contracts of the Run extraction, at the witness
runtime `AsmWit.R = toyR [] (fun _ _ => True)`, budget `0x1000`, empty live set, all-zero standard memory:
`site_no` (`newobject(Word)`), `site_wb` (`gcWriteBarrierN`, `N ≤ 8`), `site_get` (`Pool.Get` of a pool with a nil
`New` at `OA`), `site_gr` (`growslice(OA, 2, 1, 1, Word)`). `sync.(*Pool).Put`'s premise depends on the main theorem's
`T`/`Sh`; build it from `callS5` the same way.
-/

namespace FvModexp.Amd64.AsmWit

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `callS` with `RDI`, `RSI` too (five-argument runtime calls). -/
def callS5 (addr x y z w v : Nat) : State :=
  { callS addr x y z with regs := fun i => if i = 7 then BitVec.ofNat 64 w else if i = 6 then BitVec.ofNat 64 v
      else (callS addr x y z).regs i }

@[simp] theorem cs5_sp (a x y z w v : Nat) : (callS5 a x y z w v).regs 4 = BitVec.ofNat 64 CSP := rfl
@[simp] theorem cs5_mem (a x y z w v : Nat) : (callS5 a x y z w v).mem = memZ := rfl
@[simp] theorem cs5_g (a x y z w v : Nat) : (callS5 a x y z w v).regs 14 = BitVec.ofNat 64 G0 := rfl
@[simp] theorem cs5_r0 (a x y z w v : Nat) : (callS5 a x y z w v).regs 0 = BitVec.ofNat 64 x := rfl
@[simp] theorem cs5_r3 (a x y z w v : Nat) : (callS5 a x y z w v).regs 3 = BitVec.ofNat 64 y := rfl
@[simp] theorem cs5_r1 (a x y z w v : Nat) : (callS5 a x y z w v).regs 1 = BitVec.ofNat 64 z := rfl
@[simp] theorem cs5_r7 (a x y z w v : Nat) : (callS5 a x y z w v).regs 7 = BitVec.ofNat 64 w := rfl
@[simp] theorem cs5_r6 (a x y z w v : Nat) : (callS5 a x y z w v).regs 6 = BitVec.ofNat 64 v := rfl

theorem cs5_callOK (a x y z w v n : Nat) (hn : n ≤ 5) : CallOK64 (callS5 a x y z w v) 4096 n := cs_callOK a x y z n hn
theorem cs5_room (a x y z w v n : Nat) (hn : n ≤ 5) : StackRoom64 (callS5 a x y z w v) 4096 n := cs_room a x y z n hn
theorem cs5_winR (a x y z w v n : Nat) (hn : n ≤ 5) : LiveSep (liveWin64 (callS5 a x y z w v) 4096 n) R.rt :=
  cs_winR a x y z n hn
theorem cs5_inv (a x y z w v : Nat) :
    R.inv 0x1000 [] ((callS5 a x y z w v).regs 14).toNat (view R.rt [] (callS5 a x y z w v).mem) := inv0 _ bumpZ _

/-- the premise of `NewobjectLiveContract64` at a call -/
@[reducible] def noSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre64 4096 s ∧ StackRoom64 s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 1)

/-- a `newobject(Word)` call satisfies it -/
theorem site_no (addr : Nat) : noSite R addr [] 0x1000 (callS addr Extracted.dataAddr.«type:big.Word#51b931e8» 0 0) := by
  refine ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ?_, ?_, ?_⟩, cs_room _ _ _ _ 1 (by omega),
    trivial, cs_inv _ _ _ _, ?_, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  all_goals try simp only [newobjectRound64, TypeOK, cs_mem, cs_r0, BitVec.toNat_ofNat]
  all_goals first
    | decide +kernel
    | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩
    | (simp only [calleeStack64, cs_sp, BitVec.toNat_ofNat, outside_cons, outside_nil, and_true]; decide +kernel)

/-- the premise of `WbLiveContract64 … n` at a call -/
@[reducible] def wbSite (R : RtInv) (addr n : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK64 s 4096 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    LiveSep L [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] ∧
    LiveSep [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] R.rt

/-- a `gcWriteBarrierN` call satisfies it -/
theorem site_wb (addr n : Nat) : wbSite R addr n [] 0x1000 (callS addr 0 0 0) := by
  refine ⟨cs_callOK _ _ _ _ 0 (by omega), trivial, cs_inv _ _ _ _, fun r hr => absurd hr (by simp), ?_⟩
  intro x' hx
  simp only [cs_sp, List.mem_cons, List.not_mem_nil, or_false, BitVec.toNat_ofNat] at hx
  rw [rt_eq]; subst hx
  simp only [outside_cons, outside_nil, and_true, CSP, SP0, HEAP, HEND, BUMP, WBUF, HSIZE]; omega

/-- the premise of `PoolAmd64.PoolGetLive` at a call -/
@[reducible] def getSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK64 s 4096 1 ∧ StackRoom64 s 4096 1 ∧ s.mem.readLE ((s.regs 0).toNat + Pool.newOffset) 8 = 0 ∧
    LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s 4096 1)

/-- a `Pool.Get` call on the (zero) pool at `OA` satisfies it -/
theorem site_get (addr : Nat) : getSite R addr [] 0x1000 (callS addr OA 0 0) := by
  refine ⟨cs_callOK _ _ _ _ 1 (by omega), cs_room _ _ _ _ 1 (by omega), ?_,
    trivial, cs_inv _ _ _ _, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  simp only [cs_mem, cs_r0, BitVec.toNat_ofNat]; decide +kernel

/-- the premise of `GrowsliceLiveContract64` at a call -/
@[reducible] def grSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  GrowslicePre64 4096 s ∧ StackRoom64 s 4096 5 ∧
    LiveAt R addr (growsliceArgs64 s) L b (growsliceRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 5)

/-- a `growslice(OA, 2, 1, 1, Word)` call (append one word to a one-word slice) satisfies it -/
theorem site_gr (addr : Nat) :
    grSite R addr [] 0x1000 (callS5 addr OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8») := by
  refine ⟨⟨⟨cs5_callOK _ _ _ _ _ _ 5 (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => ⟨?_, ?_, ?_⟩⟩,
    cs5_room _ _ _ _ _ _ 5 (by omega), trivial, cs5_inv _ _ _ _ _ _, ?_, fun r hr => absurd hr (by simp),
    cs5_winR _ _ _ _ _ _ 5 (by omega)⟩
  all_goals try simp only [growsliceRound64, TypeOK, typPtrBytes, cs5_mem, cs5_r0, cs5_r1, cs5_r3, cs5_r6, cs5_r7,
    BitVec.toNat_ofNat]
  all_goals first
    | decide +kernel
    | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩
    | (rw [memZ_acc]; decide +kernel)
    | (simp only [calleeStack64, cs5_sp, BitVec.toNat_ofNat, outside_cons, outside_nil, and_true]; decide +kernel)

end FvModexp.Amd64.AsmWit
