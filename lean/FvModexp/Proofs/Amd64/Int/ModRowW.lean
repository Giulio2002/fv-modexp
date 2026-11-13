import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsMvz
import FvModexp.Proofs.Amd64.Nat.Free
import FvModexp.Proofs.Common.StkPool

set_option autoImplicit false

/-!
# Call-site states (amd64, Janus U-WITNESS-CALLSITE) for the `(*Int).Mod` row's extra contracts

Twin of Arm64/Int/ModRowW.lean. Companions of `AsmWit.site_mk`/`site_mv`, `Sites.site_no`/`site_wb`/`site_get` at the
witness runtime `AsmWit.R`: `site_mvz` (`memmove(OA, OB, 0)`, `MemmoveZeroLive64`; as `NatQ/DivRowWitQ`) and
`site_put` (`Pool.Put(OA, *big.stack, HEAP)`: the empty stack header at `HEAP`, a live object of a toy heap whose bump
pointer is `HEAP + 32`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy FvModexp

namespace FvModexp.Amd64.ModRowW

open FvModexp.Amd64.AsmWit

set_option maxRecDepth 100000

/-- the premise of `MemmoveZeroLive64` at a call -/
@[reducible] def mvzSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  (s.regs 1).toNat = 0 ∧ MemPre64 4096 3 s ∧
    LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3)

/-- `memmove(OA, OB, 0)` satisfies it -/
theorem site_mvz (addr : Nat) : mvzSite R addr [] 0x1000 (callS addr OA OB 0) := by
  refine ⟨by simp only [cs_r1, BitVec.toNat_ofNat], ⟨cs_sg _ _ _ _, cs_callOKm _ _ _ _ 3 (by omega), ?_⟩,
    ⟨trivial, cs_inv _ _ _ _, fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩⟩
  all_goals try simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, cs_g, cs_mem, cs_r0, cs_r1, cs_r3,
    cs_sp, BitVec.toNat_ofNat]
  all_goals first
    | (simp only [outside_cons, outside_nil, and_true]; decide)
    | (rw [memZ_acc]; decide +kernel)
    | decide

/-- the toy heap with one live 24-byte object at `HEAP` (bump pointer `HEAP + 32`), all other bytes 0 -/
def memP : Janus.Arm64.Memory := wmem (toyBytes fun a => if a = BUMP then 0x20 else 0) stdRegs

theorem bumpP : memP.readLE BUMP 8 = HEAP + 32 := by decide +kernel

theorem accP (a n : Nat) (w : Bool) : memP.accessible a n w = (wmem (fun _ => 0) stdRegs).accessible a n w :=
  acc_eq _ a n w

theorem invP (gp : Nat) : R.inv 0x1000 [(HEAP, HEAP + 24)] gp (view R.rt [(HEAP, HEAP + 24)] memP) := by
  refine toyInv_init_live (m := memP) (g := gp) (p0 := HEAP + 32) (by decide) (by decide)
    (by decide) (fun r hr => ?_) bumpP (fun i hi hi' => ?_) (by rw [accP]; decide +kernel)
    (by rw [accP]; decide +kernel) (by rw [accP]; decide +kernel)
  · simp only [List.mem_singleton] at hr; subst hr; simp only [HEAP]; omega
  · show wbytes _ i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by simp only [HEAP] at *; omega)]

/-- `Pool.Put(OA, *big.stack, HEAP)` (`RAX = p`, `RBX = type`, `RCX = data`) -/
def callP (addr : Nat) : State := { callS addr OA Free.stkT HEAP with mem := memP }

/-- the premise of `PoolAmd64.PoolPutLive … Free.stkT StkSh` at a call -/
@[reducible] def putSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat))
    (s : State) : Prop :=
  CallOK64 s 4096 3 ∧ StackRoom64 s 4096 3 ∧ (s.regs 3).toNat = Free.stkT ∧ StkSh s.mem (s.regs 1).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧ LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s 4096 3)

theorem cp_ret : memP.readLE CSP 8 = 0 := by decide +kernel

theorem cp_callOK (addr : Nat) : CallOK64 (callP addr) 4096 3 := by
  have hw : memP.accessible (CSP - 4096) (4096 + 8 + 8 * 5) true = true := by rw [accP]; decide +kernel
  have hm : (callP addr).mem = memP := rfl
  have hsp : (callP addr).regs 4 = BitVec.ofNat 64 CSP := rfl
  simp only [CallOK64, hsp, hm, csp_eq, cp_ret]
  refine ⟨by decide, by decide, by decide, by simp only [CSP, SP0]; omega, ?_⟩
  exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cp_guard (addr : Nat) : GuardOK64 (callP addr) 4096 := by
  have hm : (callP addr).mem = memP := rfl
  have hsp : (callP addr).regs 4 = BitVec.ofNat 64 CSP := rfl
  have hg : (callP addr).regs 14 = BitVec.ofNat 64 G0 := rfl
  simp only [GuardOK64, hg, hm, hsp]
  exact ⟨by decide, by rw [accP]; decide +kernel, by decide +kernel⟩

theorem cp_room (addr : Nat) : StackRoom64 (callP addr) 4096 3 := by
  have hsp : (callP addr).regs 4 = BitVec.ofNat 64 CSP := rfl
  have hg : (callP addr).regs 14 = BitVec.ofNat 64 G0 := rfl
  refine ⟨cp_guard addr, ?_⟩
  simp only [calleeStack64, hg, hsp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp only [G0, CSP, SP0]; omega

theorem cp_winR (addr : Nat) : LiveSep (liveWin64 (callP addr) 4096 3) R.rt := by
  have hsp : (callP addr).regs 4 = BitVec.ofNat 64 CSP := rfl
  intro x' hx
  simp only [liveWin64, calleeStack64, hsp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, BitVec.toNat_ofNat] at hx
  rw [rt_eq]
  rcases hx with rfl | rfl | rfl <;>
    simp only [outside_cons, outside_nil, and_true, CSP, SP0, HEAP, HEND, BUMP, WBUF, HSIZE] <;> omega

theorem site_put (addr : Nat) : putSite R addr [(HEAP, HEAP + 24)] 0x1000 [(HEAP, HEAP + 24)] (callP addr) := by
  have hm : (callP addr).mem = memP := rfl
  have hsp : (callP addr).regs 4 = BitVec.ofNat 64 CSP := rfl
  have hg : (callP addr).regs 14 = BitVec.ofNat 64 G0 := rfl
  have h0 : (callP addr).regs 0 = BitVec.ofNat 64 OA := rfl
  have h1 : (callP addr).regs 1 = BitVec.ofNat 64 HEAP := rfl
  have h3 : (callP addr).regs 3 = BitVec.ofNat 64 Free.stkT := rfl
  refine ⟨cp_callOK addr, cp_room addr, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_,
    trivial, ?_, by decide, ?_, cp_winR addr⟩
  all_goals try simp only [calleeStack64, liveWin64, LiveSep, hm, hsp, hg, h1, h3, BitVec.toNat_ofNat,
    outside_cons, outside_nil, and_true, accP, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
  all_goals first
    | decide +kernel
    | exact invP _
    | (intro r hr; subst hr; simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true];
        decide +kernel)
    | (intro r hr; rcases hr with rfl | rfl <;> (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]) <;>
        decide +kernel)
    | (intro r hr; rcases hr with rfl | rfl | rfl <;> simp only [outside_cons, outside_nil, and_true] <;>
        decide +kernel)
    | (intro r hr; exact hr)
    | (unfold Janus.Spec.Disjoint; decide +kernel)

end FvModexp.Amd64.ModRowW
