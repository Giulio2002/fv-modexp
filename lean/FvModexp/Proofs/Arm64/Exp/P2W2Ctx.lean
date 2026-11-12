import FvModexp.Proofs.Arm64.Exp.P2W2Pre
import FvModexp.Proofs.Arm64.Exp.CallW
import FvModexp.Proofs.Common.StkFrame
import FvModexp.Proofs.Arm64.Exp.LibCalls

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): call helpers (agent infra)

`ra_w2` (return addresses inside the function's segment `seg37`, base `1795088`), `cenv_of` (the callee call
environment at `SP = sp` from the entry facts and a frame of the entry memory), `obj_free` (an entry object is apart
from the stack's free part at any later point where the array is kept or fresh and the level did not drop).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

set_option maxRecDepth 20000 in
/-- a return address inside the function's own segment (`seg37`) is a return address of every callee program that
does not contain it -/
theorem ra_w2 {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 480) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (1795088 + 4 * i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg37) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x1b6410 + 4 * i < 2 ^ 48; omega) (by decide)
  simpa only [Extracted.seg37] using this

set_option maxRecDepth 20000 in
/-- the callee environment at `SP = sp` (window `[sp - K, sp + 88)`) at a memory `M` framed from the entry memory
(`ws`: the non-runtime ranges written, writable at the entry, apart from the `stackguard0` word) -/
theorem cenv_of {R : RtInv} {b : Nat} {L L1 : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat}
    {s : State} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame s.mem M (R.rt ++ ws)) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hgw : Outside (g + 16) 8 ws) (hws : ∀ r ∈ ws, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true) :
    CallW.CEnv R L1 g sp K 88 M := by
  obtain ⟨⟨-, -, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc0, hwrt, hLs, hd, -⟩, -, -, hro, -⟩ := hP
  have hout : Outside (sp - K) (K + 560) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 560 - (sp - K) = K + 560 by omega] at this
  simp only [outside_cons] at hgo
  have hgM : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := by
    refine hF.readLE _ _ ?_
    rw [outside_append]; exact ⟨hgo.2, hgw⟩
  refine ⟨hal, by omega, by omega, by rw [hF.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega),
    hg1, by rw [hF.accessible]; exact hg2, by rw [hgM]; omega, hout.of_sub (by omega) (by omega),
    by unfold Apart; omega, hgo.2, ?_, dataLoaded_frame hd hrg hro hF hws, hro⟩
  refine hx.liveSep (LiveSep.sub_win hLs (by omega) (by omega)) fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr; simp only
  exact hout.of_sub (by omega) (by omega)

/-- an entry object (`OE`) is apart from the stack's free part at a later memory where the array is kept or fresh
(relative to the entry live set) and the level did not drop -/
theorem obj_free {R : RtInv} {L : List (Nat × Nat)} {sp K st : Nat} {M0 M : Memory} {a k : Nat}
    (h : OE R L sp K st M0 a k) (hkf : ArrKF R L st M0 M) (hl : stLen M0 st ≤ stLen M st)
    (hc : stLen M st ≤ stCap M st) :
    Apart a k (free M st).1 (free M st).2 := by
  obtain ⟨h1, -, -, h4⟩ := h
  rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    simp only [free, Apart] at h4 ⊢; rw [e1, e2]; omega
  · have : a + k ≤ stW M st ∨ stW M st + 8 * stCap M st ≤ a := by
      rcases h1 with hL | hO
      · have := hap.apart_of_inRanges hL; omega
      · have := hin.apart hO; unfold Apart at this; omega
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    unfold Apart; omega

/-- `LibCalls.stkNatCall` with the `StackBackL`-ready post (`StackNat.HypL` / `PostL`) -/
theorem stkNatCallL {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat}
    (hsn : StackNat.HypL impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {st n : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (bst : st < 2 ^ 64) (bn : n < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : StackNat.Pre R b L stk above st n S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → StackNat.PostL R b L stk above st n S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (hsn b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 n))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, LibCalls.tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, trivial⟩
  · rw [LibCalls.tN bst, LibCalls.tN bn]; exact hpre
  · rw [LibCalls.tN bst, LibCalls.tN bn] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

end FvModexp.Arm64.P2W2
