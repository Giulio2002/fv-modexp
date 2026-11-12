set_option autoImplicit false

/-!
# Window-inclusion arithmetic (development: agent divmc)

A callee's arm64 window `winA S k ab = [(S.sp - k, S.sp - 8), (S.sp + 8, S.sp + ab)]` at `S.sp = sp - c` lies in the
caller's window `[sp - W, sp - 8) ∪ …` — the two `omega`s that state this inline cost 60-85 s each in big proof
contexts (profile s27: SqrBS/SqrBM/SqrKS/MulBM/MulKar); here they are closed once, in an empty context.
-/

namespace FvModexp

theorem winA_in {a n sp W c k ab : Nat} (hb : W ≤ sp) (hk : c + k ≤ W) (hab : ab + 8 ≤ c)
    (h : a + n ≤ sp - W ∨ sp - 8 ≤ a) :
    (a + n ≤ sp - c - k ∨ sp - c - 8 ≤ a) ∧ (a + n ≤ sp - c + 8 ∨ sp - c + ab ≤ a) := by omega

end FvModexp
