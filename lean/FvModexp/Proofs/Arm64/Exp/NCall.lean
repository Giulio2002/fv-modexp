import FvModexp.Proofs.Arm64.Exp.NCallP
import FvModexp.Proofs.Arm64.Exp.NEpi
import FvModexp.Proofs.Arm64.Exp.CallW

/-!
# `nat.expNN` (arm64): a call of a `NHyp.CPost` callee (`rem`, `expNNSlow`, `expNNPowerOfTwo`) to the return

`callC`: from the callee entry `S` (callee summary on `onlySegments ns`, `ns ⊆ LibN.names` without `nat.expNN`):
the call, the shared epilogue (`epi0`), the post (`post_call`). `raN`: the four return points are return addresses
for such callee programs; `keepS`: expNN's own slots (saved FP/LR, the defer flag byte) survive the callee.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- an `Ensures` on `(Extracted.program.onlySegments ns).link impl` (`ns ⊆ LibN.names`) as a `Summary` of
`LibN.program.link impl` -/
theorem hypSumN {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) {e : Nat} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) e args pre post) :
    Summary (LibN.program.link impl) e
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibN.eq_only] at hS
  exact hS

set_option maxRecDepth 20000 in
/-- the callee return points inside `nat.expNN` (`seg11`) -/
theorem raN (impl : List Segment) (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains Extracted.seg11.name = false) {r : Nat} (hr : RetPt r) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) r := by
  have hm : Extracted.seg11 ∈ Extracted.program.segments := by
    simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa only [Extracted.seg11] using CallW.retAddr_restrict hap hm hn 188 (by decide) (by decide) (by decide)
  · simpa only [Extracted.seg11] using CallW.retAddr_restrict hap hm hn 263 (by decide) (by decide) (by decide)
  · simpa only [Extracted.seg11] using CallW.retAddr_restrict hap hm hn 284 (by decide) (by decide) (by decide)
  · simpa only [Extracted.seg11] using CallW.retAddr_restrict hap hm hn 372 (by decide) (by decide) (by decide)
  · simpa only [Extracted.seg11] using CallW.retAddr_restrict hap hm hn 389 (by decide) (by decide) (by decide)

set_option maxRecDepth 20000 in
/-- expNN's slots `[sp + 1048, sp + 1064)` (saved FP/LR) and `[sp + 1168, sp + 1432)` survive a callee entered with
`SP' = sp + 1056` (window `winA S stk 112`) -/
theorem keepS {R : RtInv} {L : List (Nat × Nat)} {stk sp K zp zc zq zcq st : Nat} {M M' : Memory} {S : State}
    (hSsp : S.sp.toNat = sp + 1056) (hstk : stk ≤ K + 1056) (hK : K ≤ sp)
    (hrt : Outside (sp - K) (K + 1432) R.rt) (hzq : ZArg R L sp K zp zc zq zcq)
    (hstw : Apart st 24 (sp - K) (K + 1432))
    (harr : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - K) (K + 1432))
    (hc0 : stCap M st = 0 → stW M st = 0) (hlc : stLen M st ≤ stCap M st)
    (hF : MemFrame M M' (R.rt ++ winA S stk 112 ++ [(zq, zq + 8 * zcq)] ++ ExpHyp.stWs M st))
    {a k : Nat} (hak : (sp + 1048 ≤ a ∧ a + k ≤ sp + 1064) ∨ (sp + 1168 ≤ a ∧ a + k ≤ sp + 1432)) :
    M'.readLE a k = M.readLE a k := by
  refine Memory.readLE_congr fun i hi => ?_
  have h := hF.readLE (a + i) 1 ?_
  · simp only [Memory.readLE_one] at h; exact BitVec.eq_of_toNat_eq h
  have hrt1 : Outside (a + i) 1 R.rt := hrt.of_sub (by omega) (by omega)
  simp only [ExpHyp.stWs, stkWs, winA, hSsp, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨⟨hrt1, by omega, by omega⟩, ?_⟩, by unfold Apart at hstw; omega, ?_⟩
  · rcases hzq with ⟨h0, -⟩ | ⟨e1, e2, hzw⟩ | ⟨hin, -⟩
    · rw [h0]; omega
    · rw [e1, e2]; unfold Apart at hzw; omega
    · have := out_inR2 hrt1 hin; omega
  · rcases Nat.eq_zero_or_pos (stCap M st) with h0 | h0
    · have := hc0 h0; rw [this, h0]; omega
    · have := harr h0; unfold Apart at this; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the call of a `CPost` callee from its entry `S` to expNN's return (`Post`) -/
theorem callC (impl : List Segment) (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hn11 : ns.contains Extracted.seg11.name = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n f29 : Nat} {s S : State}
    (hs : s.sp.toNat = sp + 1312) (hal : sp % 16 = 0) (hK : K ≤ sp) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hLs : LiveSep L [(sp - K, sp + 1432)]) (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 1432))
    (hF0 : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF0 : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} {b1 zq zcq stk v cst mk : Nat}
    (hx1 : LiveExt R L L1) (hb1 : b - mk ≤ b1) (hzq : ZArg R L sp K zp zc zq zcq)
    (hstk : stk ≤ K + 1056) (h28 : S.regs 28 = s.regs 28)
    (hv : v = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n)
    (hC : mk + cst ≤ NCost costF costR costS costP xl yl n (stLen s.mem st) (Nat.log2 (natVal s.mem mp n)))
    {e r : Nat} (hr : RetPt r) {args : List (BitVec 64)} {P : State → Prop} {Q : State → State → Prop}
    (hE : Ensures ((Extracted.program.onlySegments ns).link impl) e args P Q)
    (hpc : S.pc = BitVec.ofNat 64 e) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h30 : S.regs 30 = BitVec.ofNat 64 r)
    (hargs : ArgsFrom S 0 args) (hPS : P S) (hQ : ∀ s', Q S s' → CPostG R b1 L1 stk 112 zq zcq st v cst S s')
    (harr : 0 < stCap S.mem st → Apart (stW S.mem st) (8 * stCap S.mem st) (sp - K) (K + 1432))
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0) (hlc : stLen S.mem st ≤ stCap S.mem st)
    (hacc : S.mem.accessible (sp + 1048) 256 true = true) (h29v : S.mem.readLE (sp + 1048) 8 = f29)
    (h30v : S.mem.readLE (sp + 1056) 8 = ret0) {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hS := hypSumN hap hns hE
  have hSs : S.sp.toNat = sp + 1056 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hrt : Outside (sp - K) (K + 1432) R.rt := by
    have := hrw _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  refine Reaches.call_regions (hS.withExit hret) hpc ⟨?_, hargs, hPS⟩ (fun s' hr' ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg' => ?_)
  · rw [h30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact raN impl hap hn11 hr
  have hq' := hQ s' hq
  have hq2 := hq'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hFq, -⟩ := hq2
  have kp := fun {a k : Nat} (h : (sp + 1048 ≤ a ∧ a + k ≤ sp + 1064) ∨ (sp + 1168 ≤ a ∧ a + k ≤ sp + 1432)) =>
    keepS hSs hstk hK hrt hzq hstw harr hc0 hlc hFq h
  refine hEk r s' hr (hr'.trans h30) (e1.trans hSsp) e4 e2 (by rw [hFq.accessible]; exact hacc)
    (by rw [kp (Or.inl ⟨Nat.le_refl _, by omega⟩)]; exact h29v) (by rw [kp (Or.inl ⟨by omega, by omega⟩)]; exact h30v)
    (hsl.of_rd fun a k hs => kp (by unfold Slot at hs; omega))
    fun s'' f8 f3 f4 f5 => post_call hs hK hLs hrw hsok hstw hF0 hLF0 hx1 hb1 hzq hSs hstk h28 hv hC hq' f8 f3 f4 f5

end FvModexp.Arm64.ExpN
