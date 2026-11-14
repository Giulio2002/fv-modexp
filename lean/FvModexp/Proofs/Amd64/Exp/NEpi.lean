import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): the shared epilogue after a callee (`rem`, `expNNSlow`, `expNNOdd`, `expNNPowerOfTwo`,
`expNNEven`) (agent expmc s70; twin of `Arm64.ExpN.epi0` / `EpiK`)

From a return point (`RSP = t - 0x108`): the result `AX, BX, CX` is stored to `[t - 0x58, t - 0x40)`, the defer flag
byte `t - 0x9a` (`0x6e(SP)`) is tested (0: no deferred call — the stack-given path), the result reloaded,
`ADDQ $0x100, SP; POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- the return points of the five callees (rem, slow, odd, power of two, even) -/
@[reducible] def RetPt (r : Nat) : Prop :=
  r = 6189999 ∨ r = 6190463 ∨ r = 6190629 ∨ r = 6191205 ∨ r = 6191351

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem epi0 (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (F : State → Prop) (t bp r : Nat) (M : Janus.Arm64.Memory) (hr : RetPt r)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x108) 0x110 true = true)
    (rbp : M.readLE (t - 8) 8 = bp) (rra : M.readLE t 8 = ret0) (hfl : M.readLE (t - 0x9a) 1 = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 r) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108)) (hmem : S.mem = M)
    (hK : ∀ s' : State, s'.regs 4 = BitVec.ofNat 64 (t + 8) → s'.regs 5 = BitVec.ofNat 64 bp →
      s'.regs 0 = S.regs 0 → s'.regs 3 = S.regs 3 → s'.regs 1 = S.regs 1 → s'.regs 14 = S.regs 14 →
      s'.fsBase = S.fsBase → s'.df = S.df → s'.xmm 15 = S.xmm 15 →
      MemFrame M s'.mem [(t - 0x58, t - 0x40)] → s'.mem.regions = M.regions → F s') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have es1 : BitVec.ofNat 64 (t - 0x108) + 256#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have a6e : t - 0x108 + 0x6e = t - 0x9a := by omega
  have ab0 : t - 0x108 + 0xb0 = t - 0x58 := by omega
  have ab8 : t - 0x108 + 0xb8 = t - 0x50 := by omega
  have ac0 : t - 0x108 + 0xc0 = t - 0x48 := by omega
  have rbp' : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE (t - 8) 8 = bp := by
    intro a b c
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rbp
  have rra' : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE t 8 = ret0 := by
    intro a b c
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rra
  have hfl' : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE (t - 0x9a) 1 = 0 := by
    intro a b c
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hfl
  have rd1 : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE (t - 0x58) 8 = a % 2 ^ 64 := by
    intro a b c
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
  have rd2 : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE (t - 0x50) 8 = b % 2 ^ 64 := by
    intro a b c
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have rd3 : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE (t - 0x48) 8 = c % 2 ^ 64 := by
    intro a b c
    rw [Janus.Arm64.Memory.readLE_writeLE_self]
  subst hmem
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    janus64_run [es1, es2, es3, a6e, ab0, ab8, ac0, rbp', rra', hfl', rd1, rd2, rd3]
    refine hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | rfl | (janus64_simp; done) | janus_frame | (simp only [Janus.Arm64.Memory.regions_writeLE]; done)

/-! ## The epilogue as a continuation (flag-generic chain)

As on arm64 (s26): the downstream chain is shared by the stack-given path (defer flag byte `t - 0x9a` = 0) and the
`stk == nil` path (flag 1, closure record `[t - 0x30, t - 0x18)`, closure pointer `[t - 0x10, t - 8)`, byte
`t - 0x99`); it carries those slots unchanged (`SlotEq M M0 t`) and ends in the abstract epilogue `EpiK`. -/

/-- the defer flag bytes `t - 0x9a/0x99`, the closure record `[t - 0x30, t - 0x18)` and pointer `[t - 0x10, t - 8)` -/
@[reducible] def Slot (t a k : Nat) : Prop :=
  (t - 0x9a ≤ a ∧ a + k ≤ t - 0x98) ∨ (t - 0x30 ≤ a ∧ a + k ≤ t - 0x18) ∨ (t - 0x10 ≤ a ∧ a + k ≤ t - 8)

/-- the slots of `M` are those of `M0` -/
def SlotEq (M M0 : Janus.Arm64.Memory) (t : Nat) : Prop := ∀ a k, Slot t a k → M.readLE a k = M0.readLE a k

theorem SlotEq.refl (M : Janus.Arm64.Memory) (t : Nat) : SlotEq M M t := fun _ _ _ => rfl

theorem SlotEq.of_rd {M M' M0 : Janus.Arm64.Memory} {t : Nat} (h : SlotEq M M0 t)
    (hk : ∀ a k, Slot t a k → M'.readLE a k = M.readLE a k) : SlotEq M' M0 t :=
  fun a k hs => (hk a k hs).trans (h a k hs)

theorem SlotEq.of_frame {M M' M0 : Janus.Arm64.Memory} {t : Nat} {ws : List (Nat × Nat)} (h : SlotEq M M0 t)
    (hF : MemFrame M M' ws) (ho : ∀ a k, Slot t a k → Outside a k ws) : SlotEq M' M0 t :=
  h.of_rd fun a k hs => hF.readLE a k (ho a k hs)

/-- the epilogue from a callee return point `r` (`RSP = t - 0x108`): given the post `P` at every state that differs
from the return-point state only by the result stores `[t - 0x58, t - 0x40)`, the function returns with `F` -/
def EpiK (impl : List Amd64.Segment) (ret0 : Nat) (F : State → Prop) (t bp : Nat) (r14 : BitVec 64)
    (M0 : Janus.Arm64.Memory) (P : State → Prop) : Prop :=
  ∀ (r : Nat) (S : State), RetPt r → S.rip = BitVec.ofNat 64 r → S.regs 4 = BitVec.ofNat 64 (t - 0x108) →
    S.regs 14 = r14 → S.mem.accessible (t - 0x108) 0x110 true = true → S.mem.readLE (t - 8) 8 = bp →
    S.mem.readLE t 8 = ret0 → SlotEq S.mem M0 t →
    (∀ s'' : State, MemFrame S.mem s''.mem [(t - 0x58, t - 0x40)] → s''.mem.regions = S.mem.regions →
      s''.regs 0 = S.regs 0 → s''.regs 3 = S.regs 3 → s''.regs 1 = S.regs 1 → s''.fsBase = S.fsBase →
      s''.df = S.df → s''.xmm 15 = S.xmm 15 → P s'') →
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F)

/-- the stack-given epilogue (flag 0) -/
theorem epiK0 (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (F : State → Prop) (t bp : Nat) (r14 : BitVec 64) (M0 : Janus.Arm64.Memory) (P : State → Prop)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hfl : M0.readLE (t - 0x9a) 1 = 0)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (t + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = r14 → P s'' → F s'') :
    EpiK impl ret0 F t bp r14 M0 P := by
  intro r S hr hpc hsp h14 hacc hbp hra hsl hP
  exact epi0 impl ret0 hret F t bp r S.mem hr ht1 ht2 hacc hbp hra
    ((hsl _ _ (Or.inl ⟨Nat.le_refl _, by omega⟩)).trans hfl) S hpc hsp rfl
    fun s'' f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 => hK' s'' f1 f2 (f6.trans h14) (hP s'' f10 f11 f3 f4 f5 f7 f8 f9)

end FvModexp.Amd64.ExpN
