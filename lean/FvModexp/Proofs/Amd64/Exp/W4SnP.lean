import FvModexp.Proofs.Amd64.Exp.W4Cut
import FvModexp.Proofs.Amd64.Exp.W4Own
import FvModexp.Proofs.Amd64.Exp.W4Posts2

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the `stk.nat` call's pre from the `RR`-section context (`snPre_of`) and reads through the
frame's own stores (`own_rdW`, `own_stkW`, `own_invW`) (agent expmc s53)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- a read apart from the window is kept by own stores inside `[sp - 8, sp + 0x3c0)` -/
theorem own_rdW {sp K a k : Nat} {M Mw : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M Mw ws)
    (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0) (h : AW sp K a k) : Mw.readLE a k = M.readLE a k := by
  refine hF.readLE a k (outside_ws_of_win (lo := sp - 8 - K) (hi := sp - 8 - K + (K + 968)) ?_ fun q hq => ?_)
  · simp only [AW, Apart] at h; omega
  · have := hin q hq; omega

theorem own_stkW {sp K st : Nat} {M Mw : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M Mw ws)
    (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0) (h : AW sp K st 24) :
    stW Mw st = stW M st ∧ stLen Mw st = stLen M st ∧ stCap Mw st = stCap M st :=
  ⟨own_rdW hF hin (Apart.sub h (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)),
    own_rdW hF hin (Apart.sub h (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)),
    own_rdW hF hin (Apart.sub h (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _))⟩

theorem own_invW {R : RtInv} {b g sp K : Nat} {L : List (Nat × Nat)} {M Mw : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M Mw ws) (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2) (hK : K + 8 ≤ sp)
    (hrt : Outside (sp - 8 - K) (K + 968) R.rt)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L Mw) := by
  refine FvModexp.Expmc.inv_frame hF (fun q hq => ?_) h
  have := hin q hq
  exact held_sub (Or.inr hrt) (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `stk.nat(k)` call's pre from the context -/
theorem snPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r k : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) (hserv : RunIface.Serves R)
    (hk16 : k ≤ 2 ^ 16) (hl : stLen M st + k + 3 ≤ 2 ^ 16) (hc : stackNatCost (stLen M st) k ≤ b)
    (hinv : R.inv b L g (view R.rt L M)) : SnPre R b L g fs sp st k M := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, -, harr, -, -, -, hsu, -, -, -, -, hstwb, hwba,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  exact ⟨CallW.CEnv.mono hce (by omega) (Nat.le_refl _), hserv, hsok, aw_w4 hK hstw,
    fun h => ⟨aw_w4 hK (harr h).1, (harr h).2.1⟩, hk16, hl, hc, hinv, hwba, hstwb,
    free_of_up hsu hl0 hsok.2.2.2.2.2.1⟩

end FvModexp.Amd64.W4Pro
