import FvModexp.Proofs.Arm64.Exp.NHyp

/-!
# `nat.expNN` (arm64): the callee shapes are monotone in their stack need and cost

`CPre.mono` / `CPostR.mono`; `SlowHyp.mono`: an `expNNSlow` summary with need/cost `≤ need'/cost'` is one with
`need'/cost'` (a bigger need is a stronger precondition, a bigger cost a weaker post). Used to fold the cost of the
`expNNEven` call into the slow slot of `nat.expNN`'s budget (`NCost`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.NHyp

theorem CPre.mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st : Nat}
    {ins : List (Nat × Nat)} {need cst need' cst' : Nat} {s : State} (hn : need ≤ need') (hc : cst ≤ cst')
    (h : CPre R b L stk above zp zl zc st ins need' cst' s) : CPre R b L stk above zp zl zc st ins need cst s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, by omega, a15, a16, a17, a18, a19, a20, by omega, a22⟩

theorem CPostR.mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zc st v cst cst' : Nat}
    {s s' : State} (hc : cst ≤ cst') (h : CPostR R b L stk above zp zc st v cst s s') :
    CPostR R b L stk above zp zc st v cst' s s' := by
  obtain ⟨p, l, c, q0, q1, q2, L', b', hof, ⟨hx, hb, hinv⟩, rest⟩ := h
  exact ⟨p, l, c, q0, q1, q2, L', b', hof, ⟨hx, by omega, hinv⟩, rest⟩

theorem SlowHyp.mono {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {need need' : Nat → Nat → Nat → Nat} {cost cost' : Nat → Nat → Nat → Nat → Nat}
    (h : SlowHyp impl R ns stk above need cost) (hn : ∀ a b c, need a b c ≤ need' a b c)
    (hc : ∀ l a b c, cost l a b c ≤ cost' l a b c) : SlowHyp impl R ns stk above need' cost' := by
  intro b L z zl zc st x xl xc y yl yc m ml mc
  refine (h b L z zl zc st x xl xc y yl yc m ml mc).mono (fun s hs => ?_) (fun s s' _ hq => CPostR.mono (hc _ _ _ _) hq)
  obtain ⟨h1, h2⟩ := hs
  exact ⟨CPre.mono (hn _ _ _) (hc _ _ _ _) h1, h2⟩

end FvModexp.Arm64.NHyp
