import FvModexp.Proofs.Arm64.Nat.DivMStk
import FvModexp.Proofs.Arm64.Nat.DivBig
import FvModexp.Proofs.Arm64.Nat.Free

set_option autoImplicit false

/-!
# `nat.div` (arm64), `stk == nil`, `u ≥ v`: `getStack()` = `sync.(*Pool).Get(&stackPool)` (natdiv.go:538-539, nat.go:287)

`nilG`: from `AtC` (`nat.cmp` returned `0`/`1`, `stk` slot `= 0`): `CBZ` taken, `X0 := &stackPool`, `CALL Pool.Get`
(stops at the contract entry, `X30` = `getRD` = fn+0x250). `getCallD`: the live `Pool.Get` contract with the row's shape
`StkSh` (adapted from agent expmc's `ExpN.getCall`, Arm64/Exp/NGet.lean), from `SP' = SP - 240` inside the window
`[SP - 41504, SP + 112)`, in continuation form: `KN` (the pool was empty: `X0 = X1 = 0`) or `KT` (a pooled `*stack`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

/-- the return point of the `Get` call (fn+0x250) -/
abbrev getRD : Nat := 1807440

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `stk == nil`: from `nat.cmp`'s return (`u ≥ v`) to the `Pool.Get` entry -/
theorem nilG (impl : List Segment) {zp zl zc z2 z2l z2c u ul uc v vl vc : Nat} {s : State} {S : State}
    (hS : AtC zp zl zc 0 z2 z2l z2c u ul uc v vl vc s S) (c : Nat) (hc : c ≤ 1)
    (hr0 : S.regs 0 = BitVec.ofNat 64 c)
    (hal : s.sp.toNat % 16 = 0) (hb' : 41504 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true) (Q : State → Prop)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 (cA "sync.(*Pool).Get") → X.sp = s.sp - 240#64 →
      X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 248#64 → X.regs 18 = s.regs 18 →
      X.regs 30 = BitVec.ofNat 64 getRD → X.regs 0 = BitVec.ofNat 64 Free.poolA → X.mem = S.mem →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hS.mf.accessible]; exact hw
  have m4 := hS.s4
  have hc' : (c = 0 ∨ c = 1) := by omega
  clear hS
  rcases hc' with rfl | rfl
  all_goals janus_run [hr0, m4] until [cA "sync.(*Pool).Get"]
  all_goals refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus_simp

set_option maxRecDepth 20000 in
/-- the `Get` precondition at its entry (`SP' = sp - 240`, window `[sp - 41504, sp + 112)`) -/
theorem get_preD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hKs : 41504 ≤ sp) (hsp2 : sp + 112 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - 41504) (41504 + 112) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 41504 < sp)
    (hwrt : Outside (sp - 41504) (41504 + 112) R.rt) (hgw : Apart (g + 16) 8 (sp - 41504) (41504 + 112))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - 41504, sp + 112)])
    (hok : R.ok (cA "sync.(*Pool).Get") [Free.poolA]) (hnew0 : M.readLE (Free.poolA + newOffset) 8 = 0)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (sp - 240)) (h0 : S.regs 0 = BitVec.ofNat 64 Free.poolA)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h30 : S.regs 30 = BitVec.ofNat 64 getRD) (hmem : S.mem = M) :
    CallOK S 4096 1 ∧ StackRoom S 4096 1 ∧ S.mem.readLE ((S.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R (cA "sync.(*Pool).Get") [(S.regs 0).toNat] L b 0 (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
  have esp : S.sp.toNat = sp - 240 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = Free.poolA := by rw [h0, BitVec.toNat_ofNat]; decide
  have e30 : (S.regs 30).toNat = getRD := by rw [h30, BitVec.toNat_ofNat]; decide
  subst hmem
  unfold Apart at hgw
  have h := call_pre R L b 0 (cA "sync.(*Pool).Get") [(S.regs 0).toNat] (s := S) (S := S) (lo := sp - 41504)
    (hi := sp + 112) (stack := 4096) (nargs := 1) (fr := 0) (by rw [eg]; exact hg1) (by rw [eg]; exact hg2)
    (by rw [eg, esp]; omega) (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl
    (by omega) (by rw [esp]; omega) (by rw [e30]; decide) (by rw [e30]; decide) (by decide) (by omega) (by omega)
    (by omega) (by omega) (by rw [show sp + 112 - (sp - 41504) = 41504 + 112 by omega]; exact hwacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 112 - (sp - 41504) = 41504 + 112 by omega]; exact hwrt) hLs (by rw [e0]; exact hok)
    (by rw [eg]; exact hinv) (Nat.zero_le _)
  exact ⟨h.1, h.2.1, by rw [e0]; exact hnew0, h.2.2⟩

set_option maxRecDepth 20000 in
/-- **the `Get` call** (continuation form; see the module doc) -/
theorem getCallD (impl : List Segment) (R : RtInv)
    (hget : PoolGetLive (LibDiv.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hKs : 41504 ≤ sp) (hsp2 : sp + 112 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - 41504) (41504 + 112) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 41504 < sp)
    (hwrt : Outside (sp - 41504) (41504 + 112) R.rt) (hgw : Apart (g + 16) 8 (sp - 41504) (41504 + 112))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - 41504, sp + 112)])
    (hok : R.ok (cA "sync.(*Pool).Get") [Free.poolA]) (hnew0 : M.readLE (Free.poolA + newOffset) 8 = 0)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 (cA "sync.(*Pool).Get")) (hsp : S.sp = BitVec.ofNat 64 (sp - 240))
    (h0 : S.regs 0 = BitVec.ofNat 64 Free.poolA) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h30 : S.regs 30 = BitVec.ofNat 64 getRD) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (m : Memory), S'.pc = BitVec.ofNat 64 getRD → S'.sp = S.sp → S'.regs 0 = 0#64 →
      S'.regs 1 = 0#64 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = m →
      MemFrame M m (R.rt ++ [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)]) → LiveFrame M m L [] →
      m.regions = M.regions → NewSame Free.poolA M m → R.inv b L g (view R.rt L m) →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q)
    (KT : ∀ (S' : State) (m : Memory) (d : Nat) (rs : List (Nat × Nat)), S'.pc = BitVec.ofNat 64 getRD →
      S'.sp = S.sp → S'.regs 0 = BitVec.ofNat 64 Free.stkT → S'.regs 1 = BitVec.ofNat 64 d →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = m →
      MemFrame M m (R.rt ++ [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)]) → LiveFrame M m L [] →
      m.regions = M.regions → NewSame Free.poolA M m → StkSh m d rs → FreshFrom rs L →
      (∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) →
      LiveSep rs [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)] →
      R.inv b (L ++ rs) g (view R.rt (L ++ rs) m) →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  have esp : S.sp.toNat = sp - 240 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = Free.poolA := by rw [h0, BitVec.toNat_ofNat]; decide
  have hcs : calleeStack S 4096 1 = [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)] := by
    simp only [calleeStack, esp]
    rw [show sp - 240 - 8 = sp - 248 by omega, show sp - 240 + 8 = sp - 232 by omega,
      show sp - 232 + 8 * 1 = sp - 224 by omega]
  refine ReachesRet.call_regions (hget L b) hpc
    (get_preD R b L g sp M hal hKs hsp2 hwacc hg1 hg2 hg3 hwrt hgw hgrt hLs hok hnew0 hinv S hsp h0 h28 h30 hmem)
    fun s1 hpc1 hpost hrg => ?_
  obtain ⟨r, v, fl, m, ex, ep, hs1, hMF, hLF, hNew, hcase⟩ := hpost
  rw [hcs, hmem] at hMF
  rw [hmem] at hLF hNew
  rw [e0] at hNew
  rw [eg] at hcase
  have hrg' : m.regions = M.regions := by rw [← hmem, ← hrg, hs1]
  subst hs1
  rcases hcase with ⟨hr0, hr1, hinv1⟩ | ⟨rs, hr0, hSh, hfr, hin, hsep, hinv1⟩
  · refine KN _ m (by simpa using h30) rfl ?_ ?_ (by simp [Map.keepABI]) (by simp [Map.keepABI])
      (by simp [Map.keepABI]) rfl hMF hLF hrg' hNew hinv1
    · simp only [Map.keepABI]; exact BitVec.eq_of_toNat_eq (by simpa using hr0)
    · simp only [Map.keepABI]; exact BitVec.eq_of_toNat_eq (by simpa using hr1)
  · rw [hcs] at hsep
    refine KT _ m (r 1).toNat rs (by simpa using h30) rfl ?_ ?_ (by simp [Map.keepABI]) (by simp [Map.keepABI])
      (by simp [Map.keepABI]) rfl hMF hLF hrg' hNew hSh hfr hin hsep hinv1
    · simp only [Map.keepABI, Nat.reduceEqDiff, or_self, ↓reduceIte]
      exact BitVec.eq_of_toNat_eq (by rw [hr0]; rfl)
    · simp only [Map.keepABI]; simp

end FvModexp.Arm64.NatDiv
