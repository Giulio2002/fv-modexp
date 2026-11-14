import FvModexp.Proofs.Amd64.Nat.StackNatX

set_option autoImplicit false

/-!
# Q-form budget helpers for the amd64 `P2` chain (ISA-generic part of `Arm64.P2Q`, copied verbatim by agent divmc s66)

`inv_eff`, `qstep` / `lstep`, `stkR_eq`, `effL` / `effQ` / `effN`, `grow_eff`, `effP` — see `Arm64/Exp/P2Q.lean`.
The ISA-specific `stkNatCallQ` lives in `Amd64.Exp.P2Q`.
-/

open Janus Janus.Amd64 Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Q

/-- an invariant at the real budget `b'` is one at the effective budget `b' - r` (reserve part `r ≤ b'`) -/
theorem inv_eff {R : RtInv} {b' r : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory}
    (h : R.inv b' L g v) (hr : r ≤ b') : R.inv (b' - r + r) L g v := by
  rwa [Nat.sub_add_cancel hr]

/-- the effective step after a Q-form callee charged `C` (pre `C + r ≤ b1 + r`, post `b1 + r - (C + r) + r' ≤ b'`) -/
theorem qstep {b1 C r r' b' : Nat} (h : b1 + r - (C + r) + r' ≤ b') (hc : C ≤ b1) :
    b1 - C ≤ b' - r' ∧ r' ≤ b' := by omega

/-- the effective step after a callee that keeps the stack capacity (`r` unchanged) charged `c` -/
theorem lstep {b1 c r b' : Nat} (h : b1 + r - c ≤ b') (hc : c ≤ b1) : b1 - c ≤ b' - r ∧ r ≤ b' := by omega

/-- `stkR` at a memory whose stack capacity is unchanged -/
theorem stkR_eq {H : Nat} {M M' : Memory} {st : Nat} (h : stCap M' st = stCap M st) : stkR H M' st = stkR H M st :=
  stkR_congr h

end FvModexp.Amd64.P2Q

namespace FvModexp.Amd64.P2Q

/-- the effective budget after a callee that keeps the stack capacity (`r' = r`), charged `c ≤ b1` -/
theorem effL {R : RtInv} {b1 c r r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b1 + r - c ≤ b') (hc : c ≤ b1) (hr : r' = r) : ∃ b2, R.inv (b2 + r') L g v ∧ b1 - c ≤ b2 :=
  ⟨b' - r, by rw [hr, Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

/-- the effective budget after a Q-form callee charged `C ≤ b1` (reserve `r` before, `r'` after) -/
theorem effQ {R : RtInv} {b1 C r r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b1 + r - (C + r) + r' ≤ b') (hc : C ≤ b1) : ∃ b2, R.inv (b2 + r') L g v ∧ b1 - C ≤ b2 :=
  ⟨b' - r', by rw [Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

end FvModexp.Amd64.P2Q

namespace FvModexp.Amd64.P2Q

/-- the effective budget after `stk.nat`'s Q-form post (no charge) -/
theorem effN {R : RtInv} {b1 r r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b1 + r - r + r' ≤ b') : ∃ b2, R.inv (b2 + r') L g v ∧ b1 ≤ b2 :=
  ⟨b' - r', by rw [Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

end FvModexp.Amd64.P2Q

namespace FvModexp.Amd64.P2Q

/-- an inline stack growth (`stk.reserve`'s `slices.Grow`, `growslice` charged `8 · gc`) paid by the reserve: the
budget fits, and afterwards the effective budget is not lower -/
theorem grow_eff {R : RtInv} {len n c H b gc st : Nat} {M' : Memory} {L : List (Nat × Nat)} {g : Nat} {v : Memory}
    (hc : c < len + (n + 3) / 4 * 4) (hH : len + n + 3 ≤ H) (hgc : gc = growCap8 (len + (n + 3) / 4 * 4) c) :
    8 * gc ≤ b + (stkRes H - potK * c) ∧
      (R.inv (b + (stkRes H - potK * c) - 8 * gc) L g v → stCap M' st = gc →
        ∃ b2, R.inv (b2 + stkR H M' st) L g v ∧ b ≤ b2) := by
  have hg := grow_bud len n c H (b + (stkRes H - potK * c)) hc hH (Nat.le_add_left _ _)
  rw [← hgc] at hg
  refine ⟨hg.1, fun hinv hcap => ?_⟩
  rw [stkR_of_cap hcap]
  refine ⟨b + (stkRes H - potK * c) - 8 * gc - (stkRes H - potK * gc), ?_, by omega⟩
  rw [Nat.sub_add_cancel (by omega)]; exact hinv

end FvModexp.Amd64.P2Q

namespace FvModexp.Amd64.P2Q

/-- the effective budget from a post `b - c + r' ≤ b'` (an effective-budget callee such as `P2Pre`) -/
theorem effP {R : RtInv} {b c r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b - c + r' ≤ b') : ∃ b2, R.inv (b2 + r') L g v ∧ b - c ≤ b2 :=
  ⟨b' - r', by rw [Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

end FvModexp.Amd64.P2Q
