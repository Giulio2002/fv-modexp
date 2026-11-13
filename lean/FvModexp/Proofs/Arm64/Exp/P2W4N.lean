import FvModexp.Proofs.Arm64.Exp.P2W4Ctx
import FvModexp.Proofs.Arm64.Exp.LibCalls
import FvModexp.Proofs.Arm64.Exp.P2PreX

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): `zz := stk.nat(2w)` (nat.go:993) → the entry of
`buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)` (nat.go:1153) (agent infra)

From `rsE`: `R1 = 2w`, `R0 = stk`, the call of `(*stack).nat` (return `0x1b5d3c` = 1793340, `ra_w4 103`), the spills
`zz → 280/112/120`, `powers` (`sp + 320 … sp + 704`) zeroed, the argument loads → the callee entry `1790928` with
`R0 = stk`, `R1 = sp + 320`, `R2 = R3 = 16`, `R4 = 4`, `R5 = logM`, `R6..R8 = x`, `R30 = 0x1b5d90` (1793424).
Continuation form; the stack call's post is handed on in `StackNat.PostL` form (entry state `S1` = the call state).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

/-- the continuation at the table's entry -/
@[reducible] def KPs (impl : List Segment) (R : RtInv) (H stkN aboveN b1 : Nat) (L1 : List (Nat × Nat))
    (g sp st lm xp xl xc : Nat) (M : Memory) (r18 r29 : BitVec 64) (ret0 : BitVec 64) (Q : State → Prop) : Prop :=
  ∀ (S1 s' S2 : State), S1.sp = BitVec.ofNat 64 sp → S1.regs 28 = BitVec.ofNat 64 g → S1.mem = M →
    StackNatX.PostQ R b1 L1 H stkN aboveN st (2 * W lm) S1 s' → s'.mem.regions = M.regions →
    S2.pc = BitVec.ofNat 64 1790928 → S2.sp = BitVec.ofNat 64 sp →
    S2.regs 0 = BitVec.ofNat 64 st → S2.regs 1 = BitVec.ofNat 64 (sp + 320) → S2.regs 2 = 16#64 →
    S2.regs 3 = 16#64 → S2.regs 4 = 4#64 → S2.regs 5 = BitVec.ofNat 64 lm → S2.regs 6 = BitVec.ofNat 64 xp →
    S2.regs 7 = BitVec.ofNat 64 xl → S2.regs 8 = BitVec.ofNat 64 xc → S2.regs 30 = BitVec.ofNat 64 1793424 →
    S2.regs 18 = r18 → S2.regs 28 = BitVec.ofNat 64 g → S2.regs 29 = r29 →
    MemFrame s'.mem S2.mem [(sp + 112, sp + 128), (sp + 280, sp + 288), (sp + 320, sp + 704)] →
    S2.mem.regions = s'.mem.regions →
    S2.mem.readLE (sp + 280) 8 = (s'.regs 0).toNat → S2.mem.readLE (sp + 112) 8 = 2 * W lm →
    S2.mem.readLE (sp + 120) 8 = 2 * W lm →
    ReachesRet (LibW.program.link impl) ret0 S2 Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `(*stack).nat` entry (`R30 = 1793340`) -/
theorem segN1 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (haN : aboveN ≤ 88)
    (ret0 : BitVec 64) (Q : State → Prop)
    (H b1 : Nat) (L1 : List (Nat × Nat)) (g sp st lm xp xl xc : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 848 ≤ 2 ^ 48) (hst : st < 2 ^ 48) (hlm2 : 2 ≤ lm) (hlm : lm ≤ 2 ^ 13)
    (hO : ∀ a k, sp + 88 ≤ a → a + k ≤ sp + 848 → Outside a k (R.rt ++ stkWs M st))
    (r784 : M.readLE (sp + 784) 8 = st) (r840 : M.readLE (sp + 840) 8 = lm) (r792 : M.readLE (sp + 792) 8 = xp)
    (r800 : M.readLE (sp + 800) 8 = xl) (r808 : M.readLE (sp + 808) 8 = xc)
    (hacc : M.accessible (sp + 112) 736 true = true)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 1784176) (hsp : S1.sp = BitVec.ofNat 64 sp)
    (h0 : S1.regs 0 = BitVec.ofNat 64 st) (h1 : S1.regs 1 = BitVec.ofNat 64 (2 * W lm))
    (h30 : S1.regs 30 = BitVec.ofNat 64 1793340)
    (h28 : S1.regs 28 = BitVec.ofNat 64 g) (h18 : S1.regs 18 = r18) (h29 : S1.regs 29 = r29) (hmem : S1.mem = M)
    (hpre : StackNatX.PreQ R b1 L1 H stkN aboveN st (2 * W lm) S1)
    (KP : KPs impl R H stkN aboveN b1 L1 g sp st lm xp xl xc M r18 r29 ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 S1 Q := by
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hspN : S1.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  refine LibCalls.stkNatCallQ hap hns hsn H (b := b1) (L := L1) (ra_w4 hap hnf 103 (by decide)) (by rw [hpc]; decide)
    h30 h0 h1 (by omega) (by omega) (by decide) hpre fun s' hpc' hsp' h28' h29' h18' hrg' hpost => ?_
  have hz := hpost.1 (by simp only [W]; omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hF', -, -⟩ := id hpost
  have hk : ∀ a k, sp + 88 ≤ a → a + k ≤ sp + 848 → s'.mem.readLE a k = M.readLE a k := fun a k ha1 ha2 => by
    rw [← hmem]; refine hF'.readLE a k ?_
    have := hO a k ha1 ha2
    rw [hmem]
    simp only [winA, hspN, outside_append, outside_cons, outside_nil, and_true] at this ⊢
    exact ⟨⟨this.1, by omega, by omega⟩, this.2⟩
  have q784 := (hk _ _ (by omega) (by omega)).trans r784
  have q840 := (hk _ _ (by omega) (by omega)).trans r840
  have q792 := (hk _ _ (by omega) (by omega)).trans r792
  have q800 := (hk _ _ (by omega) (by omega)).trans r800
  have q808 := (hk _ _ (by omega) (by omega)).trans r808
  have hacc' : s'.mem.accessible (sp + 112) 736 true = true := by rw [hF'.accessible, hmem]; exact hacc
  have hacc1 : s'.mem.accessible (sp + 112) 16 true = true := Memory.accessible_mono _ hacc' (by omega) (by omega)
  have hacc2 : s'.mem.accessible (sp + 280) 8 true = true := Memory.accessible_mono _ hacc' (by omega) (by omega)
  have hacc3 : s'.mem.accessible (sp + 320) 384 true = true := Memory.accessible_mono _ hacc' (by omega) (by omega)
  have hacc4 : s'.mem.accessible (sp + 760) 88 true = true := Memory.accessible_mono _ hacc' (by omega) (by omega)
  have hsp'' : s'.sp = BitVec.ofNat 64 sp := hsp'.trans hsp
  have hz' := hpost.2.1
  have hz2 := hpost.2.2.1
  generalize e0 : s'.regs 0 = z0 at hz
  have hz0 : z0.toNat < 2 ^ 64 := z0.isLt
  have hH : P2Pre.Hide (StackNatX.PostQ R b1 L1 H stkN aboveN st (2 * W lm) S1 s') := ⟨hpost⟩
  clear hpost hF' hk
  janus_run [q784, q840, q792, q800, q808, hacc1, hacc2, hacc3, hacc4] until [1790928]
  refine KP S1 s' _ hsp h28 hmem hH.h (hrg'.trans (by rw [hmem])) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?mf ?rg ?r1 ?r2 ?r3
  case mf => janus_frame
  case rg => simp only [Memory.regions_writeLE]
  case r1 =>
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, e0]
    exact Nat.mod_eq_of_lt hz0
  case r2 =>
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case r3 =>
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  all_goals first | (janus_simp; done) | skip
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18', h28', h29', h18, h28, h29]
  all_goals first | rfl | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from `rsE`** (after the reserve): `zz := stk.nat(2w)` → the table's entry -/
theorem segN {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (haN : aboveN ≤ 88)
    (ret0 : BitVec 64) (Q : State → Prop)
    (H b1 : Nat) (L1 : List (Nat × Nat)) (g sp st lm xp xl xc : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 848 ≤ 2 ^ 48) (hst : st < 2 ^ 48) (hlm2 : 2 ≤ lm)
    (hlm : lm ≤ 2 ^ 13)
    (hO : ∀ a k, sp + 88 ≤ a → a + k ≤ sp + 848 → Outside a k (R.rt ++ stkWs M st))
    (r784 : M.readLE (sp + 784) 8 = st) (r840 : M.readLE (sp + 840) 8 = lm) (r792 : M.readLE (sp + 792) 8 = xp)
    (r800 : M.readLE (sp + 800) 8 = xl) (r808 : M.readLE (sp + 808) 8 = xc)
    (hacc : M.accessible (sp + 112) 736 true = true)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 rsE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h9 : S.regs 9 = BitVec.ofNat 64 (W lm))
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hpre : ∀ S1 : State, S1.sp = BitVec.ofNat 64 sp → S1.regs 28 = BitVec.ofNat 64 g → S1.mem = M →
      StackNatX.PreQ R b1 L1 H stkN aboveN st (2 * W lm) S1)
    (KP : KPs impl R H stkN aboveN b1 L1 g sp st lm xp xl xc M (S.regs 18) (S.regs 29) ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have e2w : BitVec.ofNat 64 (W lm) + BitVec.ofNat 64 (W lm) = BitVec.ofNat 64 (2 * W lm) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize e18 : S.regs 18 = x18 at KP
  generalize e29 : S.regs 29 = x29 at KP
  janus_run [e2w] until [1784176]
  refine segN1 hap hns hnf hsn haN ret0 Q H b1 L1 g sp st lm xp xl xc M x18 x29 hal hsp1 hsp2 hst hlm2 hlm hO r784 r840
    r792 r800 r808 hacc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hpre _ ?_ ?_ ?_) KP
  all_goals first | (janus_simp; done) | skip
  all_goals first | exact hmem | skip

end FvModexp.Arm64.P2W4
