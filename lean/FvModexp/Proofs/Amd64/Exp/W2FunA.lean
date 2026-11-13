import FvModexp.Proofs.Amd64.Exp.W2Anc

set_option autoImplicit false

/-!
# window-2 (amd64): the anchored invariant `AncI` of the `W2Fun` bridge (agent expmc s63; ported from the window-4 twin)

`AncI R L0 sp K st M0 L M` = `Anc` plus the three facts every `Keeps`/`KeepsX` step of the chain posts needs to move
`Anc` (`Anc.keep`/`Anc.keepX`): the stack only grew from the anchor, it is within its capacity, and the live set is
apart from the frame window. `AncI.keep`/`AncI.keepX`: one step at any level `l` between the anchor's stack length and
the current one (scratch ranges `ex` located by `ALoc`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

/-- the anchored invariant -/
@[reducible] def AncI (R : RtInv) (L0 : List (Nat × Nat)) (sp K st : Nat) (M0 : Memory) (L : List (Nat × Nat))
    (M : Memory) : Prop :=
  Anc R L0 sp K st M0 L M ∧ stLen M0 st ≤ stLen M st ∧ stLen M st ≤ stCap M st ∧
    LiveSep L [(sp - 8 - K, sp + 0x2a8)]

theorem liveSep_of_cenv {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs (sp - 8) K 688 M) (hsp : 8 ≤ sp) : LiveSep L [(sp - 8 - K, sp + 0x2a8)] := by
  have := h.2.2.2.2.2.2.2.2.2.2.1
  rwa [show sp - 8 + 688 = sp + 0x2a8 by omega] at this

/-- the anchor itself -/
theorem AncI.refl {R : RtInv} {L0 : List (Nat × Nat)} {sp K st : Nat} {M0 : Memory}
    (hcap : stLen M0 st ≤ stCap M0 st) (hLs : LiveSep L0 [(sp - 8 - K, sp + 0x2a8)]) :
    AncI R L0 sp K st M0 L0 M0 :=
  ⟨Anc.refl R L0 sp K st M0, Nat.le_refl _, hcap, hLs⟩

/-- `AncI` through a `Keeps` step at the level `l` -/
theorem AncI.keep {R : RtInv} {L0 L L' : List (Nat × Nat)} {g fs sp K st l : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : AncI R L0 sp K st M0 L M) (hk : Keeps R L L' g fs sp K st l ex M M')
    (hl : stLen M0 st ≤ l) (hl' : l ≤ stLen M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e) (hK : K + 8 ≤ sp) :
    AncI R L0 sp K st M0 L' M' := by
  obtain ⟨hA, h1, h2, h3⟩ := hA
  have hk' := hk
  obtain ⟨-, -, k3, -, -, -, -, k8, k9, -, -, -⟩ := hk'
  exact ⟨Anc.keep hA hk hl (by omega) hex h3 hK, by omega, k8.2.2.2.2.2.1, liveSep_of_cenv k3 (by omega)⟩

/-- `AncI` through a `KeepsX` step at the level `l` -/
theorem AncI.keepX {R : RtInv} {L0 L L' : List (Nat × Nat)} {g fs sp K st l : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : AncI R L0 sp K st M0 L M) (hk : KeepsX R L L' g fs sp K st l ex M M')
    (hl : stLen M0 st ≤ l) (hl' : l ≤ stLen M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e) (hK : K + 8 ≤ sp) :
    AncI R L0 sp K st M0 L' M' := by
  obtain ⟨hA, h1, h2, h3⟩ := hA
  have hk' := hk
  obtain ⟨-, -, k3, -, -, -, -, k8, k9, -, -, -⟩ := hk'
  exact ⟨Anc.keepX hA hk hl (by omega) hex h3 hK, by omega, k8.2.2.2.2.2.1, liveSep_of_cenv k3 (by omega)⟩

/-- a stack scratch range `[l, l + k)` of the current array (above the anchor's length) is `ALoc` -/
theorem AncI.aloc {R : RtInv} {L0 L : List (Nat × Nat)} {sp K st l k : Nat} {M0 M : Memory}
    (hA : AncI R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l) (hk : 8 * l + k ≤ 8 * stCap M st) :
    ALoc R L0 st M0 (stW M st + 8 * l, k) :=
  aloc_of_anc hA.1 hl hk

end FvModexp.Amd64.W2Pro
