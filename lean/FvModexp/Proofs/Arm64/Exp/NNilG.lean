import FvModexp.Proofs.Arm64.Exp.NNilKP
import FvModexp.Proofs.Arm64.Exp.NNilND

/-!
# `nat.expNN` (arm64), `stk == nil`: the new stack (`NewStk`) from `Get` / `newobject`

* `newStk_T`: `Get` returned a pooled stack `d` (`StkSh m d rs`, fresh ranges in `R.rt`, `getCall`'s `KT`), then the
  defer record's stores (a frame apart from `R.rt`, `getT`) ⇒ `NewStk` at the memory `M'` of the join, budget kept.
* `newStk_N`: `Get` returned nil, `newobject(type:big.stack)` gave `p` (24 zeroed bytes: `cap = 0`, `ptr = 0`, `noCallN`'s
  `NewN`), then the record's stores (`joinN`) ⇒ `NewStk` with budget `b - 24`; `p ≠ 0` from `Outside 0 1 R.rt`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- a range in `R.rt` is outside frames apart from `R.rt` -/
theorem outside_of_rt {R : RtInv} {ws : List (Nat × Nat)} {a k : Nat} (hin : InRanges a k R.rt)
    (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) : Outside a k ws :=
  outside_of_forall fun r hr => by have := out_inR2 (hws r hr) hin; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem newStk_T {R : RtInv} {L : List (Nat × Nat)} {b g : Nat} {m M' : Memory} {d : Nat}
    {rs ws : List (Nat × Nat)}
    (hSh : StkSh m d rs) (hfr : FreshFrom rs L) (hin : ∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt)
    (hinv : R.inv b (L ++ rs) g (view R.rt (L ++ rs) m))
    (hF : MemFrame m M' ws) (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) :
    NewStk R L (L ++ rs) b b g M' d := by
  obtain ⟨h0, h8, h48, hacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hrs⟩ := hSh.ok
  have hhd : InRanges d 24 R.rt := by
    have := hin (d, d + 24) (by rw [hrs]; exact List.mem_cons_self ..)
    simpa only [Nat.add_sub_cancel_left] using this
  have ho := outside_of_rt hhd hws
  have ew : stW M' d = stW m d := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have el : stLen M' d = stLen m d := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have ec : stCap M' d = stCap m d := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have hrE : stkRs M' d = stkRs m d := stkRs_congr ew ec
  unfold NewStk
  rw [hrE, ← hrs, ew, el, ec]
  refine ⟨rfl, fun x hx => ⟨hin x hx, hfr x hx⟩, h0, h8, h48, by rw [hF.accessible]; exact hacc, hlen, hcap, hc0, hw8, hw48,
    fun hc => by rw [hF.accessible]; exact hwacc hc, hdis, by omega, Nat.le_refl _, ?_⟩
  exact RtInv.inv_frame' hF (fun r hr => Or.inl (hws r hr)) hinv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem newStk_N {R : RtInv} {L : List (Nat × Nat)} {b g sp : Nat} {M m M' : Memory} {p : Nat}
    {ws : List (Nat × Nat)} (hNN : NewN R b L g sp M m p) (hz : Outside 0 1 R.rt) (hb : 24 ≤ b)
    (hF : MemFrame m M' ws) (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) :
    NewStk R L (L ++ [(p, p + 24)]) b (b - 24) g M' p := by
  have ho := outside_of_rt hNN.rin hws
  have hp0 : 0 < p := by have := out_inR2 hz hNN.rin; omega
  have z0 : m.readLE p 8 = 0 := by have := hNN.zero.readLE (k := 0) (j := 8) (by omega); simpa using this
  have z8 : m.readLE (p + 8) 8 = 0 := hNN.zero.readLE (by omega)
  have z16 : m.readLE (p + 16) 8 = 0 := hNN.zero.readLE (by omega)
  have ew : stW M' p = 0 := by
    show M'.readLE p 8 = 0; rw [hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))]; exact z0
  have el : stLen M' p = 0 := by
    show M'.readLE (p + 8) 8 = 0; rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact z8
  have ec : stCap M' p = 0 := by
    show M'.readLE (p + 16) 8 = 0; rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact z16
  have hrE : stkRs M' p = [(p, p + 24)] := by simp only [stkRs, ec, ↓reduceIte]
  unfold NewStk
  rw [hrE, ew, el, ec]
  refine ⟨rfl, fun x hx => ?_, hp0, hNN.al, hNN.b48, by rw [hF.accessible]; exact hNN.acc, rfl, by decide,
    fun _ => rfl, by decide, by omega, fun h => absurd h (by decide), by unfold Apart; omega, by omega, by omega, ?_⟩
  · simp only [List.mem_singleton] at hx; subst hx
    simp only [Nat.add_sub_cancel_left]; exact ⟨hNN.rin, hNN.rap⟩
  · exact RtInv.inv_frame' hF (fun r hr => Or.inl (hws r hr)) hNN.inv

end FvModexp.Arm64.ExpN
