import FvModexp.Proofs.Arm64.Exp.P2DT
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the exit facts of a path that reuses `z` and allocates nothing (agent infra)

`post_own`: the result `(zp, l, zc)` (`z[:0]`, or `z[:1]` with `z[0] = 1`), the memory changed only in the own frame
(`ownW` = `winA`) and possibly `z`'s array → `NHyp.CPostR` with the live set and budget unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

theorem liveSep_inRanges {L w : List (Nat × Nat)} (h : LiveSep L w) {a n : Nat} (hin : InRanges a n L) :
    Outside a n w := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  exact (h r hr).of_sub h1 (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the post of an own-frame path** (see the module doc) -/
theorem post_own (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) (hA8 : 8 ≤ A) {M' : Memory} {zs : List (Nat × Nat)}
    (hF : MemFrame s.mem M' (ownW s stk A ++ zs)) (hzs : ∀ r ∈ zs, r = (zp, zp + 8 * zc) ∧ 0 < zc)
    {v l : Nat} (hl : l ≤ zc) (hv : natVal M' zp l = v) (hn : NatNorm M' zp l)
    {s' : State} (hm : s'.mem = M') (e0 : s'.regs 0 = BitVec.ofNat 64 zp) (e1 : s'.regs 1 = BitVec.ofNat 64 l)
    (e2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    NHyp.CPostR R b L stk A zp zc st v cst s s' := by
  obtain ⟨⟨-, ⟨-, hle, -, -⟩, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, ⟨hz40, hzL, hzW⟩, -, hsok, hstw, -, -, -, -, -, -, -, hzs', -,
    -, -, hinv⟩ := hP
  subst hm
  have hzout : ∀ {a k : Nat}, Outside a k [(zp, zp + 8 * zc)] → Outside a k zs := fun h =>
    outside_of_forall fun q hq => by
      obtain ⟨rfl, -⟩ := hzs q hq
      simp only [outside_cons, outside_nil, and_true] at h; exact h
  have hstz : Outside st 24 zs := outside_of_forall fun q hq => by
    obtain ⟨rfl, hc⟩ := hzs q hq
    have := (hzs' hc).1; unfold Apart at this; simp only; omega
  have hsto : Outside st 24 (ownW s stk A) := by
    simp only [win, ownW, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  have rd : ∀ o, o + 8 ≤ 24 → s'.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hsto.of_sub (by omega) (by omega), hstz.of_sub (by omega) (by omega)⟩)
  have ew : stW s'.mem st = stW s.mem st := by have := rd 0 (by omega); simpa using this
  have el : stLen s'.mem st = stLen s.mem st := rd 8 (by omega)
  have ec : stCap s'.mem st = stCap s.mem st := rd 16 (by omega)
  refine ⟨zp, l, zc, e0, e1, e2, L, b, ⟨hv, hn, hl, hz40, fun hc => ?_, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨LiveExt.refl R L, Nat.sub_le _ _, ?_⟩, ⟨⟨stkOK_hdr hsok hF ew el ec (LiveExt.refl R L), el, Or.inl ⟨ew, ec⟩⟩,
      fun hn' => absurd ⟨ew, ec⟩ hn'⟩, ?_, ?_, fun _ hn' => absurd ⟨ew, ec⟩ hn'⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hzL hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · refine Expmc.inv_frame hF (fun r hr => ?_) hinv
    rcases List.mem_append.1 hr with hr | hr
    · right
      simp only [ownW, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hw := hwrt
      rcases hr with rfl | rfl <;> simp only <;> exact hw.of_sub (by omega) (by omega)
    · obtain ⟨rfl, hc⟩ := hzs r hr
      simp only [show zp + 8 * zc - zp = 8 * zc by omega]
      exact (hzL hc).2.1
  · refine hF.mono fun a k ho => ?_
    simp only [stWs, stkWs, winA, ownW, outside_append] at ho ⊢
    exact ⟨ho.1.1.2, hzout ho.1.2⟩
  · refine ⟨fun a k hin ho => hF.readLE a k ?_⟩
    rw [outside_append] at ho ⊢
    exact ⟨by have := liveSep_inRanges hLs hin; simp only [win, ownW, outside_cons, outside_nil, and_true] at this ⊢; omega,
      hzout ho.1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the post of a path that changes only the runtime ranges and its own frame** (live objects untouched; the result
`(p, l, c)` old or fresh as `NatOF` says) -/
theorem post_rt (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {M' : Memory}
    (hF : MemFrame s.mem M' (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem M' L [])
    {L' : List (Nat × Nat)} {b' : Nat} (hx : LiveExt R L L') (hb : b - cst ≤ b')
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M')) {p l c v : Nat}
    (hof : NatOF R L L' M' zp zc 1 p l c v)
    {s' : State} (hm : s'.mem = M') (e0 : s'.regs 0 = BitVec.ofNat 64 p) (e1 : s'.regs 1 = BitVec.ofNat 64 l)
    (e2 : s'.regs 2 = BitVec.ofNat 64 c) :
    NHyp.CPostR R b L stk A zp zc st v cst s s' := by
  have hsok := hP.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.1
  subst hm
  have ho : Outside st 24 (ownW s stk A) := by
    simp only [win, ownW, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF ho
  refine ⟨p, l, c, e0, e1, e2, L', b', hof, ⟨hx, hb, hinv⟩,
    ⟨⟨stkOK_hdr hsok hF ew el ec hx, el, Or.inl ⟨ew, ec⟩⟩, fun hn' => absurd ⟨ew, ec⟩ hn'⟩, ?_,
    LiveFrame.of_nil' hLF _, fun _ hn' => absurd ⟨ew, ec⟩ hn'⟩
  refine hF.mono fun a k ho => ?_
  simp only [stWs, stkWs, winA, ownW, outside_append] at ho ⊢
  exact ⟨ho.1.1.1, ho.1.1.2⟩

end

end FvModexp.Arm64.P2D
