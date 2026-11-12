import FvModexp.Proofs.Arm64.Exp.P2PreWb

/-!
# `buildPrecomputationWindowModPower2` (arm64): reads kept by a callee (agent infra)

`pw_rd`: the `powers` array (caller memory outside the runtime, the window and every `WOK` range); `buf_rd`: a range of
`buf` apart from the callee's `z` (a `sqr` / `mul` frame `[z] ++ stWs M st`, or a `trunc` frame `[z]`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

theorem wok_pw {R : RtInv} {L : List (Nat × Nat)} {s : State} {st pw pl : Nat} {r : Nat × Nat}
    (h : WOK R L s st r) (hrt : Outside pw (24 * pl) R.rt) (hsa : StkApart s.mem st pw (24 * pl)) (hpl : 0 < pl)
    {a n : Nat} (h1 : pw ≤ a) (h2 : a + n ≤ pw + 24 * pl) (hr : r.1 < r.2) : a + n ≤ r.1 ∨ r.2 ≤ a := by
  have hs := hsa (by omega)
  rcases h hr with h | h | ⟨h, -⟩
  · have := hs.2 (by omega); unfold Apart at this; omega
  · have := hs.1; unfold Apart at this; omega
  · have := in_rt_sep h hrt hr; omega

theorem pw_rd {R : RtInv} {kc : Nat} {L L1 : List (Nat × Nat)} {s S' : State} {st pw pl : Nat}
    (hf : PF R kc L st pw pl s) (hsa : StkApart s.mem st pw (24 * pl)) (hpl : 0 < pl)
    (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) {M M' : Memory}
    (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws) {a n : Nat}
    (h1 : pw ≤ a) (h2 : a + n ≤ pw + 24 * pl) : M'.readLE a n = M.readLE a n := by
  have hw := hf.pww
  simp only [win, outside_cons, outside_nil, and_true] at hw
  exact rd_keep hf.w hsp hk ha hF hLF (Or.inr (hf.pwrt.of_sub h1 h2)) (by omega)
    fun r hr hr' => wok_pw (hws r hr) hf.pwrt hsa hpl h1 h2 hr'

theorem buf_rd {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm : Nat} {s S' : State} {bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1)
    (hf : PF R kc L st pw pl s) (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} {zp zn : Nat} (hws : ∀ r ∈ ws, r ∈ [(zp, zp + zn)] ++ stWs M st) {M' : Memory}
    (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws) {a n : Nat}
    (h1 : bp ≤ a) (h2 : a + n ≤ bp + 8 * NB pl lm) (h0 : 0 < n) (hz : Apart a n zp zn) :
    M'.readLE a n = M.readLE a n := by
  have hwok := wok_buf (zp := a) (zn := n) hc.scr h1 h2
  have hwin := wok_win hwok hf.w (by simp only; omega)
  simp only [K, A] at hwin ⊢
  exact rd_keep hf.w hsp hk ha hF hLF (hc.scr.held.sub h1 h2) (by simp only [K, A]; omega)
    fun r hr hr' => ws_apart hc.sap h1 h2 h0 hz r (hws r hr) hr'

end FvModexp.Arm64.P2Pre
