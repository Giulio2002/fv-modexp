import FvModexp.Proofs.Arm64.Nat.LibFree
import FvModexp.Proofs.Arm64.Conv
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `nat.expNN.deferwrap1` (arm64): the deferred `stk.free()` of `nat.expNN` (nat.go:337-341, 1225)

```go
func (s *stack) free() {
	s.w = s.w[:0]
	stackPool.Put(s)
}
```
The closure (frame 48, `MOVD.W R30, -48(RSP)`) reads the captured `stk` at `8(X26)`, stores `len = 0`, and calls
`sync.(*Pool).Put(&stackPool, (type:*big.stack, stk))` (`X0 = &stackPool`, `X1`/`X2` the interface words).

**Summary** (`sum`), for the live `Pool.Put` contract with element type `type:*big.stack` and any shape bound `B`
(`Pool.SliceObj B`: the header and its array are the object's ranges `rs`): from an entry state whose context
register points at a readable closure whose `stk` is a pooled-shape `*stack` owned by the caller (`rs ⊆ L`), the
closure returns with `SP`, `g`, `FP`, `R18` kept, memory changed only in `R.rt`, its window `[SP - 4144, SP - 8)`
and the `len` word, the other live objects unchanged, and the invariant for the live set WITHOUT the stack's ranges
(`dropAll L rs`: the pool owns them again).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool

namespace FvModexp.Arm64.Free

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN.deferwrap1"

/-- `type:*big.stack` (the interface type word passed to `Put`) -/
abbrev stkT : Nat := Extracted.dataAddr.«type:*big.stack#6bae7c96»
/-- `math/big.stackPool` -/
abbrev poolA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.stackPool»

/-- the captured `stk` -/
@[reducible] def stkOf (s : State) : Nat := s.mem.readLE ((s.regs 26).toNat + 8) 8

/-- The context of a call of the closure (`B` = the pool shape's capacity bound, `rs` = the stack's ranges). -/
def Pre (R : RtInv) (b : Nat) (L rs : List (Nat × Nat)) (B : Nat) (s : State) : Prop :=
  GuardOK s 4144 ∧ StackOK s 4144 0 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    (s.regs 26).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 26).toNat + 8) 8 false = true ∧
    Apart ((s.regs 26).toNat + 8) 8 (s.sp.toNat - 4144) 4144 ∧
    SliceObj B s.mem (stkOf s) rs ∧ Apart (stkOf s) 24 (s.sp.toNat - 4144) 4144 ∧
    Apart (stkOf s + 8) 8 ((s.regs 28).toNat + 16) 8 ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4144 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    (∀ r ∈ rs, r ∈ L) ∧ R.ok (cA "sync.(*Pool).Put") [poolA] ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    LiveSep L [(s.sp.toNat - 4144, s.sp.toNat)] ∧ Outside (s.sp.toNat - 4144) 4144 R.rt

/-- What it guarantees. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L rs : List (Nat × Nat)) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29) ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (stkOf s + 8, stkOf s + 16)]) ∧
    LiveFrame s.mem s'.mem L [(stkOf s + 8, stkOf s + 16)] ∧
    R.inv b (dropAll L rs) (s.regs 28).toNat (view R.rt (dropAll L rs) s'.mem)

/-- `len = 0` stored into a pooled-shape header keeps the shape. -/
theorem sliceObj_len0 {B : Nat} {m m' : Memory} {d : Nat} {rs ws : List (Nat × Nat)} (h : SliceObj B m d rs)
    (hf : MemFrame m m' ws) (hd0 : Outside d 8 ws) (hd16 : Outside (d + 16) 8 ws) (h0 : m'.readLE (d + 8) 8 = 0) :
    SliceObj B m' d rs := by
  unfold SliceObj at h ⊢
  obtain ⟨h0', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have e0 : m'.readLE d 8 = m.readLE d 8 := hf.readLE _ _ hd0
  have e2 : m'.readLE (d + 16) 8 = m.readLE (d + 16) 8 := hf.readLE _ _ hd16
  simp only [e0, e2, h0, hf.accessible]
  exact ⟨h0', h1, h2, h3, Nat.zero_le _, h5, h6, h7, h8, h9, h10, h11⟩

/-- the return site of the `Put` call -/
abbrev pPR : Nat := segAddr Extracted.program fn + 0x34

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sum (impl : List Segment) (R : RtInv) (B : Nat)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R stkT (SliceObj B))
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibFree.program.link impl) (segAddr Extracted.program fn) (Pre R b L rs B) (Post R b L rs) := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hc1, hc2, hca, hsh, hsw, hsg, hgw, hgr, hrs, hok, hinv,
    hLs, hout⟩
  have hca' := hca; have hsw' := hsw; have hsg' := hsg; have hgw' := hgw
  unfold Apart at hca' hsw' hsg' hgw'
  have hsh' := hsh
  obtain ⟨hs0, hs8, hs48, hsacc, -, -, -, -, -, -, -, -⟩ := hsh'
  simp only [stkOf] at hsh hsw' hsg' hs0 hs8 hs48 hsacc
  have hacc8 : s.mem.accessible (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8) 8 true = true :=
    Memory.accessible_mono _ hsacc (by omega) (by omega)
  janus_run [hacc8] until [cA "sync.(*Pool).Put"]
  generalize hM1 : ((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 56) 8
      (s.regs 29).toNat).writeLE (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8) 8 0 = M1
  have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF1 : MemFrame s.mem M1 [(s.sp.toNat - 56, s.sp.toNat - 40),
      (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8, s.mem.readLE ((s.regs 26).toNat + 8) 8 + 16)] := by
    rw [← hM1]; janus_frame
  have hk1 : ∀ a n, (a + n ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 40 ≤ a) →
      (a + n ≤ s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8 ∨ s.mem.readLE ((s.regs 26).toNat + 8) 8 + 16 ≤ a) →
      M1.readLE a n = s.mem.readLE a n := fun a n h1 h2 =>
    hF1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2⟩)
  have hlen0 : M1.readLE (s.mem.readLE ((s.regs 26).toNat + 8) 8 + 8) 8 = 0 := by
    rw [← hM1, Memory.readLE_writeLE_self]
  have hhdr : (s.mem.readLE ((s.regs 26).toNat + 8) 8, s.mem.readLE ((s.regs 26).toNat + 8) 8 + 24) ∈ L := by
    apply hrs; have h' := hsh; unfold SliceObj at h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e⟩ := h'
    rw [e]; exact List.mem_cons_self
  have hinv1 : R.inv b L (s.regs 28).toNat (view R.rt L M1) := by
    refine RtInv.inv_frame' hF1 (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · right; exact ⟨_, hhdr, by simp only; omega, by simp only; omega⟩
  have hsh1 : SliceObj B M1 (s.mem.readLE ((s.regs 26).toNat + 8) 8) rs :=
    sliceObj_len0 hsh hF1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega) hlen0
  refine ReachesRet.call (hput L b rs) rfl ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩,
    ?_, ?_, hrs, ?_, ?_, ?_, ?_, ?_⟩ ?_
  all_goals try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hsp48]
  case refine_3 => omega
  case refine_4 => omega
  case refine_6 => omega
  case refine_7 => rw [← hM1]; simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  case refine_8 => omega
  case refine_9 => rw [← hM1]; simp only [Memory.accessible_writeLE]; exact hg2
  case refine_10 => rw [hk1 _ _ (by omega) (by omega)]; omega
  case refine_11 => simp only [calleeStack, hsp48, outside_cons, outside_nil, and_true]; omega
  case refine_13 =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsh1
  case refine_14 => exact hok
  case refine_15 => exact hinv1
  case refine_16 => exact Nat.zero_le _
  case refine_17 =>
    intro r hr; have := hLs r hr
    simp only [calleeStack, hsp48, outside_cons, outside_nil, and_true] at this ⊢; omega
  case refine_18 =>
    intro r hr
    simp only [calleeStack, hsp48, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  all_goals first | decide | rfl | skip
  intro s2 hpc2 ⟨r, v, fl, m, ex, ep, hs2, hMF, hLF, hNew, hinv2⟩
  subst hs2
  simp only [calleeStack, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hsp48] at hMF hpc2
  have hkm : ∀ a, (s.sp.toNat - 56 ≤ a ∧ a + 8 ≤ s.sp.toNat - 40) → m.readLE a 8 = M1.readLE a 8 := fun a ha =>
    hMF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)
  have r56 : m.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat := by
    rw [hkm _ (by omega), ← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  have r48 : m.readLE (s.sp.toNat - 48) 8 = (s.regs 30).toNat := by
    rw [hkm _ (by omega), ← hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (BitVec.isLt _)]
  janus_run [r56, r48, hsp48]
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [setReg_apply, Map.keepABI_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · simp only [setReg_apply, Map.keepABI_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · refine hF1.trans hMF fun a k ho => ?_
    simp only [stkOf, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1, h2⟩ := ho
    exact ⟨⟨by omega, h2⟩, hrt, by omega, by omega⟩
  · refine ⟨fun a k hin hws => ?_⟩
    simp only [stkOf, outside_cons, outside_nil, and_true] at hws
    obtain ⟨r0, hr0, i1, i2⟩ := hin
    have := hLs r0 hr0
    simp only [outside_cons, outside_nil, and_true] at this
    rw [hLF.readLE a k ⟨r0, hr0, i1, i2⟩ trivial,
      hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, hws⟩)]
  · exact hinv2

end FvModexp.Arm64.Free
