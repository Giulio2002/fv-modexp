import FvModexp.Proofs.Arm64.Witness.Sites
import FvModexp.Proofs.Arm64.Nat.Free
import FvModexp.Proofs.Common.StkPool

set_option autoImplicit false

/-!
# Call-site states (arm64, Janus U-WITNESS-CALLSITE) for the `(*Int).Mod` row's extra contracts

Companions of `AsmWit.site_mk`/`site_mv`, `Sites.site_cl`/`site_wb`/`site_gr` at the witness runtime `AsmWit.R`:
`site_mz` (`memmove(OA, OB, 0)`, `MemmoveZeroLive`), `site_no` (`newobject(Word)`), `site_get` (`Pool.Get` of the
zero pool at `OA`), `site_put` (`Pool.Put(OA, *big.stack, HEAP)`: the empty stack header at `HEAP`, a live object of
a toy heap whose bump pointer is `HEAP + 32`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

namespace FvModexp.Arm64.AsmWit

set_option maxRecDepth 100000

/-- `memmove(OA, OB, 0)` satisfies `MemmoveZeroLive`'s premise -/
theorem site_mz (addr : Nat) : ((callS addr OA OB 0).regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 (callS addr OA OB 0) ∧
    LiveMemAt R addr [((callS addr OA OB 0).regs 0).toNat, ((callS addr OA OB 0).regs 1).toNat,
      ((callS addr OA OB 0).regs 2).toNat] [] 0x1000 (callS addr OA OB 0) (calleeStack (callS addr OA OB 0) 4096 3) :=
  ⟨by rw [cs_r2]; decide, ⟨(guardOK_iff _ _).1 (cs_room addr _ _ _ 3 (by omega)).1, cs_callOK _ _ _ _ 3 (by omega),
      (cs_room addr _ _ _ 3 (by omega)).2⟩,
    ⟨trivial, cs_inv _ _ _ _, fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩⟩

/-- the premise of `NewobjectLiveContract` at a call -/
@[reducible] def noSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1)

/-- a `newobject(Word)` call satisfies it -/
theorem site_no (addr : Nat) : noSite R addr [] 0x1000 (callS addr Extracted.dataAddr.«type:big.Word#51b931e8» 0 0) := by
  refine ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ?_, ?_, ?_⟩, cs_room _ _ _ _ 1 (by omega),
    trivial, cs_inv _ _ _ _, ?_, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  all_goals try simp only [newobjectRound, TypeOK, cs_mem, cs_r0, BitVec.toNat_ofNat]
  all_goals first
    | decide +kernel
    | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩
    | (simp only [calleeStack, cs_sp, BitVec.toNat_ofNat, outside_cons, outside_nil, and_true]; decide +kernel)

/-- the premise of `PoolGetLive` at a call -/
@[reducible] def getSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s 4096 1 ∧ StackRoom s 4096 1 ∧ s.mem.readLE ((s.regs 0).toNat + Pool.newOffset) 8 = 0 ∧
    LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s 4096 1)

/-- a `Pool.Get` call on the (zero) pool at `OA` satisfies it -/
theorem site_get (addr : Nat) : getSite R addr [] 0x1000 (callS addr OA 0 0) := by
  refine ⟨cs_callOK _ _ _ _ 1 (by omega), cs_room _ _ _ _ 1 (by omega), ?_,
    trivial, cs_inv _ _ _ _, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  simp only [cs_mem, cs_r0, BitVec.toNat_ofNat]; decide +kernel

/-- the toy heap with one live 24-byte object at `HEAP` (bump pointer `HEAP + 32`), all other bytes 0 -/
def memP : Memory := wmem (toyBytes fun a => if a = BUMP then 0x20 else 0) stdRegs

theorem bumpP : memP.readLE BUMP 8 = HEAP + 32 := by decide +kernel

theorem invP (gp : Nat) : R.inv 0x1000 [(HEAP, HEAP + 24)] gp (view R.rt [(HEAP, HEAP + 24)] memP) := by
  refine toyInv_init_live (m := memP) (g := gp) (p0 := HEAP + 32) (by decide) (by decide)
    (by decide) (fun r hr => ?_) bumpP (fun i hi hi' => ?_) (by unfold memP; rw [acc_eq]; decide +kernel)
    (by unfold memP; rw [acc_eq]; decide +kernel) (by unfold memP; rw [acc_eq]; decide +kernel)
  · simp only [List.mem_singleton] at hr; subst hr; simp only [HEAP]; omega
  · show wbytes _ i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [HEAP] at *; omega)]

/-- `Pool.Put(OA, *big.stack, HEAP)` -/
def callP (addr : Nat) : State := { callS addr OA Free.stkT HEAP with mem := memP }

/-- the premise of `PoolPutLive … Free.stkT StkSh` at a call -/
@[reducible] def putSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat))
    (s : State) : Prop :=
  CallOK s 4096 3 ∧ StackRoom s 4096 3 ∧ (s.regs 1).toNat = Free.stkT ∧ StkSh s.mem (s.regs 2).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧ LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s 4096 3)

theorem accP (a n : Nat) (w : Bool) : memP.accessible a n w = (wmem (fun _ => 0) stdRegs).accessible a n w :=
  acc_eq _ a n w

theorem site_put (addr : Nat) : putSite R addr [(HEAP, HEAP + 24)] 0x1000 [(HEAP, HEAP + 24)] (callP addr) := by
  have hm : (callP addr).mem = memP := rfl
  have hsp : (callP addr).sp = BitVec.ofNat 64 (SP0 - 16) := rfl
  have hg : (callP addr).regs 28 = BitVec.ofNat 64 G0 := rfl
  have hlr : (callP addr).regs 30 = BitVec.ofNat 64 RET := rfl
  have h0 : (callP addr).regs 0 = BitVec.ofNat 64 OA := rfl
  have h1 : (callP addr).regs 1 = BitVec.ofNat 64 Free.stkT := rfl
  have h2 : (callP addr).regs 2 = BitVec.ofNat 64 HEAP := rfl
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_,
    trivial, ?_, by decide, ?_, cs_winR addr OA Free.stkT HEAP 3 (by omega)⟩
  all_goals try simp only [CallOK, GuardOK, calleeStack, LiveSep, hm, hsp, hg, hlr, h0, h1, h2, BitVec.toNat_ofNat,
    outside_cons, outside_nil, and_true, accP, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
  all_goals first
    | decide +kernel
    | exact invP _
    | (intro r hr; subst hr; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (intro r hr; rcases hr with rfl | rfl <;> (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]) <;>
        decide +kernel)
    | (intro r hr; exact hr)
    | (unfold Disjoint; decide +kernel)

end FvModexp.Arm64.AsmWit
