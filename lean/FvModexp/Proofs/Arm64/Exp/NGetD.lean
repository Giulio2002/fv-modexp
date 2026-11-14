import FvModexp.Proofs.Arm64.Exp.NStkNilD
import FvModexp.Proofs.Common.StkPool

/-! Definitions and helper lemmas of `NGet.lean` (split out, top s47: the module and its LibNE twin import this instead of each other / the original, so they compile in parallel). `Get`'s return point and the `Get` call precondition. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

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

end FvModexp.Arm64.ExpN
