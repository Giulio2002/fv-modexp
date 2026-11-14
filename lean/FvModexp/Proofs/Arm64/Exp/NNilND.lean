import FvModexp.Proofs.Arm64.Exp.NGetD

/-! Definitions and helper lemmas of `NNilN.lean` (split out, top s47: the module and its LibNE twin import this instead of each other / the original, so they compile in parallel). `newobject(type:big.stack)`: addresses, descriptor facts, precondition, result record. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- `runtime.newobject` -/
abbrev noA : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- the type descriptor `type:big.stack` (`newobject`'s argument at fn+0x260) -/
abbrev stkTy : Nat := Extracted.dataAddr.«type:big.stack#c761f19c»

theorem stkTy_v : stkTy = 2764768 := rfl

/-- `newobject`'s return point (fn+0x26c) -/
abbrev noR : Nat := 1787164

theorem stkTy_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE stkTy 8 = 24 ∧ m.readLE (stkTy + 8) 8 = 8 ∧ m.accessible stkTy 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

theorem blockSize_stk : blockSize 24 false = 24 := by decide

set_option maxRecDepth 20000 in
/-- the `newobject(type:big.stack)` precondition from `SP' = sp + 1056` -/
theorem noPreN (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hK : 4304 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 1432) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 1432) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 1432))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hd : Extracted.program.DataLoaded M) (hsv : RunIface.Serves R)
    (hinv : R.inv b L g (view R.rt L M)) (hb : 24 ≤ b)
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h0 : S.regs 0 = BitVec.ofNat 64 stkTy)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h30 : S.regs 30 = BitVec.ofNat 64 noR) (hmem : S.mem = M) :
    NewobjectPre 4096 S ∧ StackRoom S 4096 1 ∧
      LiveAt R noA [(S.regs 0).toNat] L b (newobjectRound S) (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
  have esp : S.sp.toNat = sp + 1056 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = stkTy := by rw [h0, stkTy_v]; rfl
  have e30 : (S.regs 30).toNat = noR := by rw [h30, BitVec.toNat_ofNat]; decide
  obtain ⟨ht1, ht2, ht3⟩ := stkTy_facts hd
  have hround : newobjectRound S = 24 := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, e0, hmem, ht1, ht2]; decide
  subst hmem
  unfold Apart at hgw
  have h := call_pre R L b (newobjectRound S) noA [(S.regs 0).toNat] (s := S) (S := S) (lo := sp - K)
    (hi := sp + 1432) (stack := 4096) (nargs := 1) (fr := 0) (by rw [eg]; exact hg1) (by rw [eg]; exact hg2)
    (by rw [eg, esp]; omega) (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl
    (by omega) (by rw [esp]; omega) (by rw [e30]; decide) (by rw [e30]; decide) (by decide) (by omega) (by omega)
    (by omega) (by omega) (by rw [show sp + 1432 - (sp - K) = K + 1432 by omega]; exact hwacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 1432 - (sp - K) = K + 1432 by omega]; exact hwrt) hLs (hsv.2.2.2.2.1 _)
    (by rw [eg]; exact hinv) (by rw [hround]; exact hb)
  refine ⟨⟨h.1, ⟨by rw [e0, stkTy_v]; decide, by rw [e0]; exact ht3⟩, ?_, ?_⟩, h.2.1, h.2.2⟩
  · simp only [typSize, e0, ht1, maxAlloc]; omega
  · rw [e0]
    exact outside_calleeStack_of_data hd (by decide +kernel) (by rw [esp]; omega)
      (by rw [esp]; exact Memory.accessible_mono _ hwacc (by omega) (by omega))

/-- what `newobject(type:big.stack)` gives (`p` the object) -/
structure NewN (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M m : Memory) (p : Nat) : Prop where
  mf : MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)])
  lf : LiveFrame M m L []
  rg : m.regions = M.regions
  rin : InRanges p 24 R.rt
  b48 : p + 24 ≤ 2 ^ 48
  acc : m.accessible p 24 true = true
  al : p % 8 = 0
  zero : ZeroBytes m p 24
  rap : ApartAll p 24 L
  cap : ApartAll p 24 [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)]
  inv : R.inv (b - 24) (L ++ [(p, p + 24)]) g (view R.rt (L ++ [(p, p + 24)]) m)

end FvModexp.Arm64.ExpN
