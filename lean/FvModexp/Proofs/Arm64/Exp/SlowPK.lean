import FvModexp.Proofs.Arm64.Exp.SlowJ
import FvModexp.Proofs.Arm64.Exp.SlowPR
import FvModexp.Proofs.Arm64.Exp.SlowAl

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the prologue join `KM` (`MV = fnE + 0xec`) and its destination facts (agent expmc)

`KM`: after `z.make(len x)` (nat.go:58-69): the context `JC`, the destination `z = (X0, X5 = len x, X2 = cap)` a `DL`
with `len x ≤ cap`, `X1 = len x`, `X4 = x.ptr`, `X3 = stk`, `X7`/`X8` = `y`. `dl_reuse` (the entry `z` array,
`len x ≤ cap z`) and `dl_fresh` (a `makeslice` array, fresh relative to the entry live set) build its `DL`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- at `MV` (`fnE + 0xec`) -/
structure KM (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (z zc' : Nat) :
    Prop where
  pc : S.pc = BitVec.ofNat 64 mvJ
  jc : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1
  dz : DL R L st zp zc S.mem L1 z zc'
  lz : xl ≤ zc'
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e1 : S.regs 1 = BitVec.ofNat 64 xl
  e2 : S.regs 2 = BitVec.ofNat 64 zc'
  e3 : S.regs 3 = BitVec.ofNat 64 st
  e4 : S.regs 4 = BitVec.ofNat 64 xp
  e5 : S.regs 5 = BitVec.ofNat 64 xl
  e7 : S.regs 7 = BitVec.ofNat 64 yp
  e8 : S.regs 8 = BitVec.ofNat 64 yl

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

/-- the stack header is kept by the prologue's frame writes -/
theorem hdr_fw (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FWp sp)) :
    stW M st = stW s.mem st ∧ stLen M st = stLen s.mem st ∧ stCap M st = stCap s.mem st := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hhd : Outside st 24 (FWp sp) := by simp only [FWp, outside_cons, outside_nil, and_true]; omega
  exact ⟨hF.readLE _ _ (hhd.of_sub (by omega) (by omega)), hF.readLE _ _ (hhd.of_sub (by omega) (by omega)),
    hF.readLE _ _ (hhd.of_sub (by omega) (by omega))⟩

set_option maxRecDepth 20000 in
/-- **reuse**: the entry `z` array (`0 < cap z`) is a destination after the prologue's frame writes -/
theorem dl_reuse (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FWp sp)) (hc0 : 0 < zc) : DL R L st zp zc M L zp zc := by
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsok := hP.stk0
  obtain ⟨e0, e1, e2⟩ := hdr_fw hP hF
  obtain ⟨⟨hH, -, -, hfr⟩, acc, b48, al, -⟩ := hz hc0
  refine ⟨hzc, fun _ => ⟨al, hH, by rw [hF.accessible]; exact acc, b48⟩, Or.inl ⟨rfl, rfl, hc0⟩, fun _ => ⟨hH, ?_, ?_⟩,
    fun h => absurd h (by omega)⟩
  · show Apart zp (8 * zc) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    rw [e0, e1, e2]; exact hfr
  · intro hin hap; exact (hfresh hH hap hin).symm

set_option maxRecDepth 20000 in
/-- **fresh**: a `makeslice` array `[p, p + r)` of capacity `c` (`8c ≤ r`), allocated at memory `M` (live set `L`,
the stack untouched since the entry) is a destination at `m` (live set `L ++ [(p, p + r)]`) -/
theorem dl_fresh (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M m : Memory} {b1 : Nat}
    (hw : WC R L K g sp st zp zc s.mem M L b1 (stLen s.mem st)) {p r c : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem M L b1 (stLen s.mem st) m p r (8 * c)) (hc40 : c < 2 ^ 40)
    (hc0 : 0 < c) : DL R L st zp zc m (L ++ [(p, p + r)]) p c := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 544) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h8c : 8 * c ≤ r := hA.sz
  have hhd : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    hA.rdH _ _ (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart at hstw ⊢; omega)
  have e0 : stW m st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen m st = stLen M st := hhd 8 (by omega)
  have e2 : stCap m st = stCap M st := hhd 16 (by omega)
  have hx : LiveExt R L (L ++ [(p, p + r)]) :=
    LiveExt.single (by rw [show p + r - p = r by omega]; exact hA.rin)
      (by rw [show p + r - p = r by omega]; exact hA.rap)
  have hin : InRanges p (8 * c) R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  have hap1 : ApartAll p (8 * c) L := fun x hx' => by
    have := hA.rap x hx'; unfold Apart at this ⊢; omega
  have hheld : Held R (L ++ [(p, p + r)]) p (8 * c) :=
    Or.inl ⟨(p, p + r), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by simp only; omega⟩
  have hsb : StackBack R L (L ++ [(p, p + r)]) st M m :=
    ⟨hA.wc.sok, e1, Or.inl ⟨e0, e2⟩⟩
  refine ⟨hc40, fun _ => ⟨hA.al, hheld, Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega), by
      have := hA.b48; omega⟩, Or.inr (Or.inl ⟨hin, hap1⟩), fun _ => ?_, fun h => absurd h (by omega)⟩
  exact ob_fresh (L := L) hw.sok (WC.cap0 hP hw) hsb hin hap1 hheld (fun _ hne => absurd ⟨e0, e2⟩ hne) hc0

end

end FvModexp.Arm64.ExpSlow
