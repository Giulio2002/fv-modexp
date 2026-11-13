import FvModexp.Proofs.Amd64.Exp.W4XnA
import FvModexp.Proofs.Amd64.Exp.W4DivP

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# window-4 prologue (amd64): the facts at path A's division call `q.div(stk, z2, x, m)` (`dvgPre_of`; agent expmc s56)

From the context `CtxX` (extra range `q`), the quotient `q` (`k` words, `len = cap = k`), the remainder buffer `z2`
(`n` words in the stack above the context's level) and the dividend `x` (an object of the context) to `DvPreG`.
Every non-trivial field is a small lemma over explicit facts (no `omega` over the 54-conjunct context).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- a range inside the stack's used part above `l0` ends inside the part above `l0` -/
theorem in_upK {p q st l0 : Nat} {M : Memory}
    (h : stW M st + 8 * l0 ≤ p ∧ p + q ≤ stW M st + 8 * stLen M st) (hlc : stLen M st ≤ stCap M st) :
    p + q ≤ (stUp M st l0).1 + (stUp M st l0).2 := by
  simp only [stUp]; omega

/-- a range inside the stack's used part lies inside the whole array -/
theorem in_arrK {p q st l0 : Nat} {M : Memory}
    (h : stW M st + 8 * l0 ≤ p ∧ p + q ≤ stW M st + 8 * stLen M st) (hlc : stLen M st ≤ stCap M st) :
    stW M st ≤ p ∧ p + q ≤ stW M st + 8 * stCap M st := by
  omega

/-- a range in the used part or apart from the whole array is apart from the free part -/
theorem freeK {p q st l0 : Nat} {M : Memory}
    (hB : (stW M st + 8 * l0 ≤ p ∧ p + q ≤ stW M st + 8 * stLen M st) ∨ Apart p q (stW M st) (8 * stCap M st))
    (hlc : stLen M st ≤ stCap M st) : Apart p q (stFree M st).1 (stFree M st).2 := by
  rcases hB with h | h
  · exact apFree h.2
  · exact arrFree h hlc

theorem n40 {n : Nat} (h : n ≤ 128) : n < 2 ^ 40 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path A's division pre from the context (memory at the call) -/
theorem dvgPre_of {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r stkD qp k z2p xp xl xc : Nat} {M : Memory}
    (hC : CtxX R L g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r [(qp, 8 * k)] M)
    (hk40 : k < 2 ^ 40) (hqL : NatLive M R L qp k) (hqW : AW sp K qp (8 * k)) (hqG : Apart qp (8 * k) (g + 16) 8)
    (hqF : Apart qp (8 * k) (fs - 8) 8) (hqS : Apart qp (8 * k) st 24)
    (hqB : (stW M st + 8 * l0 ≤ qp ∧ qp + 8 * k ≤ stW M st + 8 * stLen M st) ∨
      Apart qp (8 * k) (stW M st) (8 * stCap M st))
    (hqz : Apart qp (8 * k) z2p (8 * n))
    (hzin : stW M st + 8 * l0 ≤ z2p ∧ z2p + 8 * n ≤ stW M st + 8 * stLen M st) (hz8 : z2p % 8 = 0)
    (hxO : Obj R L sp K st l0 [(qp, 8 * k)] M xp (8 * xl)) (hxa : M.accessible xp (8 * xl) false = true)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxN : NatNorm M xp xl) (hxl9 : xl ≤ 2 ^ 9)
    (hKD : stkD ≤ K) (hserv : RunIface.Serves R)
    (w0 : M.readLE sp 8 = xp) (w1 : M.readLE (sp + 8) 8 = xl) (w2 : M.readLE (sp + 16) 8 = xc)
    (w3 : M.readLE (sp + 24) 8 = mp) (w4 : M.readLE (sp + 32) 8 = n) (w5 : M.readLE (sp + 40) 8 = mc)
    (hsl : stLen M st + 16 * xl + 64 ≤ 2 ^ 16) (hcF : costF (stLen M st) xl n ≤ costD)
    (hcb : costD ≤ b) (hinv : R.inv b L g (view R.rt L M)) :
    DvPreG R b costF costD L g fs sp K stkD st qp k k z2p n n xp xl xc mp n mc M := by
  obtain ⟨-, hce, -, -, hn, hn128, -, -, hm, hmO, -, hnm, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, hcap, harr, hug, huf, huw, hsu, hstg, hstf, hgl, hgO, hstwb, -,
    -, -, -, -, -, -, -, -, -, -, -, hstnz⟩ := hC
  have hlc : stLen M st ≤ stCap M st := hsok.2.2.2.2.2.1
  obtain ⟨la8, lah, laacc, la48⟩ := hsok.2.2.2.2.1 hcap
  have hza : (stUp M st l0).1 ≤ z2p := hzin.1
  have hzb := in_upK hzin hlc
  have hzw := in_arrK hzin hlc
  have hex : (qp, 8 * k) ∈ [(qp, 8 * k)] := List.mem_singleton_self _
  obtain ⟨o1, o2, o3, o4, o5⟩ := hxO
  refine ⟨hce, hKD, hserv, globals_win hgl hKD, hn128, hn, w0, w1, w2, w3, w4, w5,
    Nat.le_refl _, Nat.le_refl _,
    ⟨hk40, hqL, fun _ => ⟨hqW, hqG, hqF, (hgO.2.2.2.2 _ hex).symm⟩⟩,
    ⟨n40 hn128, fun _ => ⟨hz8, held_sub lah hzw.1 hzw.2, M.accessible_sub laacc (Or.inr rfl) hzw.1 hzw.2,
      Nat.le_trans hzw.2 la48⟩,
      fun _ => ⟨apIn huw.symm hza hzb (Nat.le_refl _), apIn hug.symm hza hzb (Nat.le_refl _),
        apIn huf.symm hza hzb (Nat.le_refl _), apIn hgO.2.2.2.1 hza hzb (Nat.le_refl _)⟩⟩,
    hxl9, hxa, hx48, o1, o2,
    hm.1, hm.2.1, hm.2.2.1, hmO.2.1, hxN, hnm, hsok, hstw, fun h => ⟨(harr h).1, (harr h).2.1⟩,
    hsl, hcap, o3, free_of_up o4 hl0 hlc, hmO.2.2.1, free_of_up hmO.2.2.2.1 hl0 hlc,
    fun _ _ => hqz, fun p c hp _ => ?_,
    hstnz, hgO.2.2.1.symm, hstg, hstwb, free_of_up hsu hl0 hlc, hstf,
    (free_of_up huf.symm hl0 hlc).symm, (free_of_up hgO.2.2.2.1 hl0 hlc).symm, hcF, hcb, hinv⟩
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(o5 _ hex).symm, (hmO.2.2.2.2 _ hex).symm, hqS, freeK hqB hlc⟩
  · exact ⟨apIn o4 hza hzb (Nat.le_refl _), apIn hmO.2.2.2.1 hza hzb (Nat.le_refl _), apIn hsu hza hzb (Nat.le_refl _),
      apFree hzin.2⟩

end FvModexp.Amd64.W4Pro
