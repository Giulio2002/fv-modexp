import FvModexp.Proofs.Arm64.NatQ.RemDefs
import FvModexp.Proofs.Arm64.Nat.Callees

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/RemCall.lean, TIGHT COSTS, asm s38)
# `nat.rem` (arm64): the two calls — `q := stk.nat(k)` (`natc`) and `_, r = q.div(stk, z, u, v)` (`divc`)

Both stop at the callee entry and take the callee's precondition as a hypothesis about the CALL state (proved by pure
lemmas elsewhere); the continuation gets the callee's post.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.NatRem
open FvModexp.Arm64.NatRem
variable {H : Nat}

theorem pw_forall {α : Type} {R : α → α → Prop} (hR : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a}, a ∈ l → ∀ {b}, b ∈ l → a ≠ b → R a b
  | [], _, _, ha, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, h, a, ha, b, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 _ hb'
    · exact hR (h.1 _ ha')
    · exact pw_forall hR h.2 ha' hb' hne

set_option maxRecDepth 20000 in
/-- a return site inside `nat.rem`'s segment is admissible for a callee program that does not keep it -/
theorem raR (impl : List Segment) (hap : ImplApart Extracted.program impl) (ns : List String)
    (hn : ns.contains fn = false) (ret : Nat) (hal : ret % 4 = 0) (h1 : 0x1b9040 ≤ ret) (h2 : ret < 0x1b9040 + 4 * 91)
    (hst : ∀ st ∈ Extracted.program.stubs, st.addr ≠ ret) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) ret := by
  have hmem : Extracted.seg19 ∈ Extracted.program.segments := by
    have : Extracted.program.segments[19]'(by decide) = Extracted.seg19 := rfl
    rw [← this]; exact List.getElem_mem _
  have hb : Extracted.seg19.base = 0x1b9040 := rfl
  have hl : Extracted.seg19.words.length = 91 := rfl
  have hnm : Extracted.seg19.name = fn := rfl
  refine RetAddr.of_placement hal (by omega) ⟨_, hmem, by rw [hb]; omega, by rw [hb, hl]; omega⟩ hap.1 ?_ hst
  intro seg hm hc
  by_cases he : seg = Extracted.seg19
  · subst he; rw [hnm, hn] at hc; exact absurd hc (by decide)
  · have hpw := (List.pairwise_append.1 hap.1).1
    have := pw_forall (fun {a b} h => by unfold Segment.Apart at h ⊢; omega) hpw hm hmem he
    unfold Segment.Apart at this; rw [hb, hl] at this; omega

set_option linter.defProp false in
/-- `(*stack).nat`'s `ensL` as a summary on `LibRem` -/
def snsum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) :=
  StackNatX.sumQ impl hap R hgr hmc hwb H b L st n LibRem.names (sub_of_all (by decide))

set_option linter.defProp false in
/-- `nat.div` (premise `DHyp`) as a summary on `LibRem` -/
def dvsum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {cd : Nat → Nat → Nat} (hD : DHyp impl R cd)
    (H b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64) :=
  Ensures.toSummaryIn (hD H b L z zl zc st z2 z2l z2c u ul uc v vl vc) (noExit_restrict hap LibDiv.names)
    (show CodeIn ((Extracted.program.onlySegments LibDiv.names).link impl) (LibRem.program.link impl) by
      rw [LibRem.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`CALL (*stack).nat`** (state `P`): the call, the post handed on at the return `T` -/
theorem natc (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st k : Nat) (hst : st < 2 ^ 64) (hk : k < 2 ^ 64) (P : State) (ret : W64)
    (hpc : P.pc = BitVec.ofNat 64 callNat) (r0 : P.regs 0 = BitVec.ofNat 64 st) (r1 : P.regs 1 = BitVec.ofNat 64 k)
    (hpre : StackNatX.PreQ R b L H 4208 24 st k P) (Q : State → Prop)
    (kk : ∀ T, T.pc = BitVec.ofNat 64 (callNat + 4) → T.sp = P.sp → T.regs 28 = P.regs 28 → T.regs 29 = P.regs 29 →
      T.regs 18 = P.regs 18 → T.mem.regions = P.mem.regions →
      StackNatX.PostQ R b L H 4208 24 st k P T → ReachesRet (LibRem.program.link impl) ret T Q) :
    ReachesRet (LibRem.program.link impl) ret P Q := by
  janus_run until [segAddr Extracted.program StackNat.fn]
  refine ReachesRet.call_regions (snsum impl hap R hgr hmc hwb H b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 k)) rfl
    ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 (callNat + 4) : BitVec 64).toNat = callNat + 4 := by decide
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [e30]; exact raR impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom, setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    exact ⟨r0, r1, trivial⟩
  case pre =>
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt hk]
    exact hpre
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt hk] at hq
  refine kk T (by rw [hT]; simp only [setReg_apply, ↓reduceIte]) f1 ?_ ?_ ?_ hrg hq
  · rw [f2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · rw [f3]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · rw [f4]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]

end FvModexp.Arm64.Q.NatRem
