import FvModexp.Proofs.Arm64.Nat.DivBasicNat
import FvModexp.Proofs.Arm64.Nat.DivBasicLay

/-!
# `divBasic` (arm64): after `stk.nat` — `vn1 := v[n-1]`, `rec := reciprocalWord(vn1)`, `j := m`, `ujn := 0`, to the
loop head (natdiv.go:654-662)

`pro3a`: from the return of `stk.nat` (`AfterNat`) to the return of `reciprocalWord`; `pro3b`: to the loop head, where
`Env` and `Mem` hold (handed to a continuation).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

theorem LiveFrame.trans' {m1 m2 m3 : Memory} {L ws : List (Nat × Nat)} (h1 : LiveFrame m1 m2 L ws)
    (h2 : LiveFrame m2 m3 L ws) : LiveFrame m1 m3 L ws :=
  ⟨fun a n hin ho => (h2.readLE a n hin ho).trans (h1.readLE a n hin ho)⟩

/-- `Env` from `stk.nat`'s post (pure) -/
theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (hpre : Pre R b L qp ql st up ul uc vp vl s) {S2 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hext : LiveExt R L L1) (hbud : b - ExpHyp.stackNatCost (stLen s.mem st) (vl + 1) ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen s.mem st + (vl + 1 + 3) / 4 * 4)
    (hsame : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st → stW S2 st = stW s.mem st ∧ stCap S2 st = stCap s.mem st)
    (hgrow : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = s.mem.accessible a n v) :
    Env R b L qp ql st up ul uc vp vl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have hscr := Scr.of_post (m0 := s.mem) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_⟩
  · rw [← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hacc2]; exact a3, a4⟩

end FvModexp.Arm64.DivBasic
