import FvModexp.Proofs.Arm64.Witness.AsmWit

/-!
# More call-site states of the runtime contracts (arm64; Janus U-WITNESS-CALLSITE)

The arm64 twin of `Amd64/Witness/Sites.lean` (agent divmc): companions of `AsmWit.site_mv`/`site_mk` at the witness
runtime `AsmWit.R`, budget `0x1000`, empty live set, all-zero standard memory: `site_cl` (`memclrNoHeapPointers(OA, 8)`),
`site_wb` (`gcWriteBarrierN`), `site_gr` (`growslice(OA, 2, 1, 1, Word)`).
-/

namespace FvModexp.Arm64.AsmWit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

set_option maxRecDepth 100000

/-- `callS` with `X3`, `X4` too (five-argument runtime calls). -/
def callS5 (addr x y z w v : Nat) : State :=
  { callS addr x y z with regs := fun i => if i = 3 then BitVec.ofNat 64 w else if i = 4 then BitVec.ofNat 64 v
      else (callS addr x y z).regs i }

@[simp] theorem cs5_sp (a x y z w v : Nat) : (callS5 a x y z w v).sp = BitVec.ofNat 64 (SP0 - 16) := rfl
@[simp] theorem cs5_mem (a x y z w v : Nat) : (callS5 a x y z w v).mem = memZ := rfl
@[simp] theorem cs5_g (a x y z w v : Nat) : (callS5 a x y z w v).regs 28 = BitVec.ofNat 64 G0 := rfl
@[simp] theorem cs5_lr (a x y z w v : Nat) : (callS5 a x y z w v).regs 30 = BitVec.ofNat 64 RET := rfl
@[simp] theorem cs5_r0 (a x y z w v : Nat) : (callS5 a x y z w v).regs 0 = BitVec.ofNat 64 x := rfl
@[simp] theorem cs5_r1 (a x y z w v : Nat) : (callS5 a x y z w v).regs 1 = BitVec.ofNat 64 y := rfl
@[simp] theorem cs5_r2 (a x y z w v : Nat) : (callS5 a x y z w v).regs 2 = BitVec.ofNat 64 z := rfl
@[simp] theorem cs5_r3 (a x y z w v : Nat) : (callS5 a x y z w v).regs 3 = BitVec.ofNat 64 w := rfl
@[simp] theorem cs5_r4 (a x y z w v : Nat) : (callS5 a x y z w v).regs 4 = BitVec.ofNat 64 v := rfl

/-- the premise of `MemclrNoHeapPointersLive` at a call -/
@[reducible] def clSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  Mem.EqPre 4096 2 s ∧
  LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s 4096 2) ∧
  LiveDest R L s 4096 2 (s.regs 0).toNat (s.regs 1).toNat

/-- a `memclrNoHeapPointers(OA, 8)` call satisfies it -/
theorem site_cl (addr : Nat) : clSite R addr [] 0x1000 (callS addr OA 8 0) := by
  have hcs : calleeStack (callS addr OA 8 0) 4096 2 =
      [(SP0 - 16 - 4096, SP0 - 16 - 8), (SP0 - 16 + 8, SP0 - 16 + 8 + 16)] := rfl
  refine ⟨⟨(guardOK_iff _ _).1 (cs_guard _ _ _ _), cs_callOK _ _ _ _ 2 (by omega), ?_⟩,
    ⟨trivial, cs_inv _ _ _ _, fun r hr => by simp at hr, cs_winR _ _ _ _ 2 (by omega)⟩,
    ⟨?_, ?_, ?_, Or.inr ?_⟩⟩
  all_goals simp only [hcs, cs_g, cs_mem, cs_r0, cs_r1, cs_r2, BitVec.toNat_ofNat]
  all_goals first
    | (simp only [outside_cons, outside_nil, and_true]; decide)
    | (rw [memZ_acc]; decide +kernel)
    | decide
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide)

/-- the premise of `WbLiveContract … n` at a call -/
@[reducible] def wbSite (R : RtInv) (addr n : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s 4096 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    LiveSep L [(s.sp.toNat - 4096, s.sp.toNat - 8)] ∧ LiveSep [(s.sp.toNat - 4096, s.sp.toNat - 8)] R.rt

/-- a `gcWriteBarrierN` call satisfies it -/
theorem site_wb (addr n : Nat) : wbSite R addr n [] 0x1000 (callS addr 0 0 0) := by
  refine ⟨cs_callOK _ _ _ _ 0 (by omega), trivial, cs_inv _ _ _ _, fun r hr => absurd hr (by simp), ?_⟩
  intro x' hx
  simp only [cs_sp, List.mem_cons, List.not_mem_nil, or_false, BitVec.toNat_ofNat] at hx
  rw [rt_eq]; subst hx
  simp only [outside_cons, outside_nil, and_true, SP0, HEAP, HEND, BUMP, WBUF, HSIZE]; omega

/-- the premise of `GrowsliceLiveContract` at a call -/
@[reducible] def grSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
    LiveAt R addr (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 5)

theorem cs5_callOK (a x y z w v : Nat) : CallOK (callS5 a x y z w v) 4096 5 := by
  simp only [CallOK, cs5_lr, cs5_sp, cs5_mem, BitVec.toNat_ofNat]; rw [memZ_acc]; decide +kernel

/-- a `growslice(OA, 2, 1, 1, Word)` call (append one word to a one-word slice) satisfies it -/
theorem site_gr (addr : Nat) :
    grSite R addr [] 0x1000 (callS5 addr OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8») := by
  have hcs : calleeStack (callS5 addr OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8») 4096 5 =
      [(SP0 - 16 - 4096, SP0 - 16 - 8), (SP0 - 16 + 8, SP0 - 16 + 8 + 40)] := rfl
  refine ⟨⟨⟨cs5_callOK _ _ _ _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩,
    trivial, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [hcs, growsliceRound, TypeOK, typSize, typPtrBytes, GuardOK, cs5_mem, cs5_r0,
    cs5_r1, cs5_r2, cs5_r3, cs5_r4, cs5_g, cs5_sp, BitVec.toNat_ofNat]
  all_goals first
    | decide +kernel
    | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩
    | (rw [memZ_acc]; decide +kernel)
    | exact inv0 _ bumpZ _
    | (intro r hr; simp at hr; done)
    | (simp only [outside_cons, outside_nil, and_true]; decide)
    | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide))

end FvModexp.Arm64.AsmWit
