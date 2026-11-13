import FvModexp.Proofs.Amd64.Exp.W2Ctx

set_option autoImplicit false

/-!
# window-2 prologue (amd64): the frame's own stores keep the `RR`-section context (`keeps_own`)
(agent expmc s52; twin of the first half of `Arm64.W2Sn2K`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

theorem outside_ws_of_win {a k lo hi : Nat} (h : a + k ≤ lo ∨ hi ≤ a) :
    ∀ {ws : List (Nat × Nat)}, (∀ r ∈ ws, lo ≤ r.1 ∧ r.2 ≤ hi) → Outside a k ws
  | [], _ => trivial
  | (l1, h1) :: ws, hin => by
    have := hin (l1, h1) (List.mem_cons_self ..)
    simp only at this
    exact ⟨by omega, outside_ws_of_win h (fun r hr => hin r (List.mem_cons_of_mem _ hr))⟩

theorem stkOK_frame {R : RtInv} {L : List (Nat × Nat)} {st : Nat} {M M' : Memory} (h : StkOK M R L st)
    (e0 : M'.readLE st 8 = M.readLE st 8) (e1 : M'.readLE (st + 8) 8 = M.readLE (st + 8) 8)
    (e2 : M'.readLE (st + 16) 8 = M.readLE (st + 16) 8) (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w) :
    StkOK M' R L st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [StkOK, stW, stLen, stCap, NatLive] at h5 h6 h7 ⊢
  rw [e0, e1, e2, hacc, hacc]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the frame's own stores (inside `[sp - 8, sp + 0x2a8)`, off the kept slots) keep the context -/
theorem keeps_own {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hreg : M'.regions = M.regions)
    (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x2a8) (hsl : ∀ j, KeptJ j → Outside (sp + j) 8 ws) :
    Keeps R L L g fs sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have hin' : ∀ q ∈ ws, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp - 8 + 688 := fun q hq => by have := hin q hq; omega
  have ow : ∀ a k, Apart a k (sp - 8 - K) (K + 688) → Outside a k ws := fun a k h =>
    outside_ws_of_win (by unfold Apart at h; omega) hin'
  have hst : Apart st 24 (sp - 8 - K) (K + 688) := hstw
  have e0 := hF.readLE st 8 (ow _ _ (hst.mono (by omega) (Nat.le_refl _)))
  have e1 := hF.readLE (st + 8) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have e2 := hF.readLE (st + 16) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have hsok' := stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w)
  refine keeps_of hce (LiveExt.refl R L) (FvModexp.Expmc.frame_widen_rt hF)
    (FvModexp.Expmc.liveFrame_of_frame (ws := ([] : List (Nat × Nat))) hF (fun a k hin2 _ => ?_)) hreg ?_
    (ow _ _ hga) (ow _ _ f6) (fun a k ho => ⟨ow _ _ ho.2.1, trivial⟩) hsl hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _) (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
    (arrIn_kept ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
  · obtain ⟨q, hq, h1, h2⟩ := hin2
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this
    exact outside_ws_of_win (lo := sp - 8 - K) (hi := sp - 8 + 688) (by omega) hin'
  · intro q hq hlt
    have := hin q hq
    exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)

end FvModexp.Amd64.W2Pro
