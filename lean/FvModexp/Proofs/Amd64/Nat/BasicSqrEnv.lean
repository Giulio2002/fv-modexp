import FvModexp.Proofs.Amd64.Nat.BasicSqrStep

/-!
# `basicSqr` (amd64): `Env` from `(*stack).nat`'s postcondition (pure; the amd64 twin of `Arm64/Nat/BasicSqrEnv.lean`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.BasicSqr

theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (hpre : Pre R b L st zp zl zc xp xl s) (hbig : 12 ≤ xl) {P S2 : Memory}
    (hPs : ∀ k, k + 8 ≤ 24 → P.readLE (st + k) 8 = s.mem.readLE (st + k) 8)
    (hPacc : ∀ a n v, P.accessible a n v = s.mem.accessible a n v)
    {L1 : List (Nat × Nat)} {b1 : Nat} (hext : LiveExt R L L1)
    (hbud : b - stackNatCost (stLen P st) (2 * xl) ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen P st + (2 * xl + 3) / 4 * 4)
    (hsame : stLen P st + (2 * xl + 3) / 4 * 4 ≤ stCap P st → stW S2 st = stW P st ∧ stCap S2 st = stCap P st)
    (hgrow : stCap P st < stLen P st + (2 * xl + 3) / 4 * 4 → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = P.accessible a n v)
    (hmem : stCap P st < stLen P st + (2 * xl + 3) / 4 * 4 → (stW S2 st, stW S2 st + 8 * stCap S2 st) ∈ L1)
    (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    Env R b L st zp zl zc xp xl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have eW : stW P st = stW s.mem st := hPs 0 (by omega)
  have eL : stLen P st = stLen s.mem st := hPs 8 (by omega)
  have eC : stCap P st = stCap s.mem st := hPs 16 (by omega)
  rw [eW, eL, eC] at hsame
  rw [eL, eC] at hgrow hmem
  rw [eL] at hlen hbud
  have hscr := Scr.of_post (m0 := s.mem) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, hbig, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_, ?_, hx15, hdf, hra⟩
  · rw [← hPacc, ← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + (2 * xl + 3) / 4 * 4 ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hPacc, ← hacc2]; exact a3, a4⟩
  · intro hn
    by_cases hc : stLen s.mem st + (2 * xl + 3) / 4 * 4 ≤ stCap s.mem st
    · exact absurd (hsame hc) hn
    · exact hmem (by omega)

end FvModexp.Amd64.BasicSqr
