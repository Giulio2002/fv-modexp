import FvModexp.Proofs.Arm64.Exp.NStkNil
import FvModexp.Proofs.Common.StkPool

/-!
# `nat.expNN` (arm64), `stk == nil`: the call `sync.(*Pool).Get(&stackPool)` of `getStack()` (nat.go:287)

From the `Get` entry `getA` (`NStkNil.stkNil`'s `KG`: `X0 = &stackPool`, `X30` = fn+0x234, `SP = SP' = sp + 1056`) over
the live `Pool.Get` contract with the row's pool shape `StkSh` (coordinator decision on "[expmc s25] PROPOSAL") to its
return point fn+0x234, in continuation form: `KN` (the pool was empty: `X0 = X1 = 0`, invariant for `L`) or `KT`
(`X0 = type:*big.stack`, `X1 = d` a pooled `*stack` of shape `StkSh` with ranges `rs`, fresh wrt `L`, inside `R.rt`,
apart from the callee window; invariant for `L ++ rs`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool FvModexp

namespace FvModexp.Arm64.ExpN

/-- the return point of the `Get` call (fn+0x234) -/
abbrev getR : Nat := 1787108

set_option maxRecDepth 20000 in
/-- the `Get` precondition at its entry (from `SP' = sp + 1056`, expNN's window `[sp - K, sp + 1432)`) -/
theorem get_pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hK : 4304 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 1432) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 1432) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 1432))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hok : R.ok getA [Free.poolA]) (hnew0 : M.readLE (Free.poolA + newOffset) 8 = 0)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h0 : S.regs 0 = BitVec.ofNat 64 Free.poolA)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h30 : S.regs 30 = BitVec.ofNat 64 getR) (hmem : S.mem = M) :
    CallOK S 4096 1 ∧ StackRoom S 4096 1 ∧ S.mem.readLE ((S.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R getA [(S.regs 0).toNat] L b 0 (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
  have esp : S.sp.toNat = sp + 1056 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = Free.poolA := by rw [h0, BitVec.toNat_ofNat]; decide
  have e30 : (S.regs 30).toNat = getR := by rw [h30, BitVec.toNat_ofNat]; decide
  subst hmem
  unfold Apart at hgw
  have h := call_pre R L b 0 getA [(S.regs 0).toNat] (s := S) (S := S) (lo := sp - K) (hi := sp + 1432)
    (stack := 4096) (nargs := 1) (fr := 0) (by rw [eg]; exact hg1) (by rw [eg]; exact hg2)
    (by rw [eg, esp]; omega) (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl
    (by omega) (by rw [esp]; omega) (by rw [e30]; decide) (by rw [e30]; decide) (by decide) (by omega) (by omega)
    (by omega) (by omega) (by rw [show sp + 1432 - (sp - K) = K + 1432 by omega]; exact hwacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 1432 - (sp - K) = K + 1432 by omega]; exact hwrt) hLs (by rw [e0]; exact hok)
    (by rw [eg]; exact hinv) (Nat.zero_le _)
  exact ⟨h.1, h.2.1, by rw [e0]; exact hnew0, h.2.2⟩

set_option maxRecDepth 20000 in
/-- **the `Get` call** (continuation form; see the module doc) -/
theorem getCall (impl : List Segment) (R : RtInv)
    (hget : PoolGetLive (LibN.program.link impl) getA 4096 R Free.stkT StkSh)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hK : 4304 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 1432) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 1432) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 1432))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hok : R.ok getA [Free.poolA]) (hnew0 : M.readLE (Free.poolA + newOffset) 8 = 0)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 getA) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 Free.poolA) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h30 : S.regs 30 = BitVec.ofNat 64 getR) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (m : Memory), S'.pc = BitVec.ofNat 64 getR → S'.sp = S.sp → S'.regs 0 = 0#64 →
      S'.regs 1 = 0#64 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = m →
      MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)]) → LiveFrame M m L [] →
      m.regions = M.regions → NewSame Free.poolA M m → R.inv b L g (view R.rt L m) →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KT : ∀ (S' : State) (m : Memory) (d : Nat) (rs : List (Nat × Nat)), S'.pc = BitVec.ofNat 64 getR →
      S'.sp = S.sp → S'.regs 0 = BitVec.ofNat 64 Free.stkT → S'.regs 1 = BitVec.ofNat 64 d →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = m →
      MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)]) → LiveFrame M m L [] →
      m.regions = M.regions → NewSame Free.poolA M m → StkSh m d rs → FreshFrom rs L →
      (∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) →
      LiveSep rs [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)] →
      R.inv b (L ++ rs) g (view R.rt (L ++ rs) m) →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have esp : S.sp.toNat = sp + 1056 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = Free.poolA := by rw [h0, BitVec.toNat_ofNat]; decide
  have hcs : calleeStack S 4096 1 = [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)] := by
    simp only [calleeStack, esp]
  refine Reaches.call_regions (Summary.withExit (hget L b) hret) hpc
    (get_pre R b L K g sp M hal hK hKs hsp2 hwacc hg1 hg2 hg3 hwrt hgw hgrt hLs hok hnew0 hinv S hsp h0 h28 h30 hmem)
    fun s1 hpc1 hpost hrg => ?_
  obtain ⟨r, v, fl, m, ex, ep, hs1, hMF, hLF, hNew, hcase⟩ := hpost
  rw [hcs, hmem] at hMF
  rw [hmem] at hLF hNew
  rw [e0] at hNew
  rw [eg] at hcase
  have hrg' : m.regions = M.regions := by rw [← hmem, ← hrg, hs1]
  subst hs1
  rcases hcase with ⟨hr0, hr1, hinv1⟩ | ⟨rs, hr0, hSh, hfr, hin, hsep, hinv1⟩
  · refine KN _ m (by simpa using hpc1) rfl ?_ ?_ (by simp [Map.keepABI]) (by simp [Map.keepABI])
      (by simp [Map.keepABI]) rfl hMF hLF hrg' hNew hinv1
    · simp only [Map.keepABI]; exact BitVec.eq_of_toNat_eq (by simpa using hr0)
    · simp only [Map.keepABI]; exact BitVec.eq_of_toNat_eq (by simpa using hr1)
  · rw [hcs] at hsep
    refine KT _ m (r 1).toNat rs (by simpa using hpc1) rfl ?_ ?_ (by simp [Map.keepABI]) (by simp [Map.keepABI])
      (by simp [Map.keepABI]) rfl hMF hLF hrg' hNew hSh hfr hin hsep hinv1
    · simp only [Map.keepABI]; exact BitVec.eq_of_toNat_eq (by rw [hr0]; rfl)
    · simp only [Map.keepABI]; simp

end FvModexp.Arm64.ExpN
