import FvModexp.Proofs.Arm64.Nat.KSqrCall

/-!
# `karatsubaSqr` (arm64): `z0.abs = z0.abs.sqr(stk, x0.abs)` (natmul.go:300), `0x1bc4ac` → `0x1bc4d0`

From the boundary after `clear(z)` (`z[0:2n] = 0`): the call (`ks_sqcall`; `z0 = z[0:2·n2]` reused, exactly
`z[0:2·len x0]` written, holding `x0²`), then the stores of the result into `z0`'s header.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- the operand facts of `x0 = x[:len x0]` -/
theorem KM.x0ops {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    lx0 ≤ xc ∧ xc < 2 ^ 40 ∧ M.accessible xp (8 * lx0) false = true ∧
      (0 < xc → Held R Lk xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48) ∧ (0 < lx0 → Outside xp (8 * lx0) (win s W 48)) ∧
      (0 < lx0 → StkSep M st xp (8 * lx0)) ∧ Apart zp (8 * zc) xp (8 * lx0) := by
  have hxc : n ≤ xc := h.pre.2.2.2.2.2.2.1
  have hxc40 : xc < 2 ^ 40 := h.pre.2.2.2.2.2.2.2.1
  have hxacc : s.mem.accessible xp (8 * n) false = true := h.pre.2.2.2.2.2.2.2.2.2.1
  have hxh : Held R L xp (8 * xc) := h.pre.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := h.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxw : Outside xp (8 * n) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzx : Apart zp (8 * zc) xp (8 * n) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxs : StkSep s.mem st xp (8 * n) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 := h.l0
  simp only [kn2] at hl0
  have hacc : M.accessible xp (8 * lx0) false = true := by
    rw [h.fr.accessible]; exact Memory.accessible_sub _ hxacc (Or.inl rfl) (by omega) (by omega)
  refine ⟨by omega, hxc40, hacc, fun _ => ⟨h.ext.held hxh, hx48⟩, fun _ => hxw.of_sub (by omega) (by omega),
    fun _ => h.sepOf (hxs.sub (by omega)) (hxh.sub (by omega) (by omega)), by unfold Apart at hzx ⊢; omega⟩

/-- `z`'s array facts at `M` -/
theorem KM.zops {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    zc < 2 ^ 40 ∧ NatLive M R Lk zp zc ∧ Outside zp (8 * zc) (win s W 48) ∧
      Apart zp (8 * zc) (guard s) 8 ∧ StkSep M st zp (8 * zc) ∧ zp + 8 * zc ≠ xp + 8 * xc ∧ 2 * n ≤ zc ∧
      zp % 8 = 0 ∧ Held R Lk zp (8 * zc) ∧ zp + 8 * zc ≤ 2 ^ 48 := by
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc40 : zc < 2 ^ 40 := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzlive : NatLive s.mem R L zp zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzw : Outside zp (8 * zc) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg : Apart zp (8 * zc) (guard s) 8 := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzs : StkSep s.mem st zp (8 * zc) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hne : zp + 8 * zc ≠ xp + 8 * xc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h80 := h.lay.2.2.2.2.1
  obtain ⟨hal, hh, hacc, h48⟩ := hzlive (by omega)
  exact ⟨hzc40, fun _ => ⟨hal, h.ext.held hh, by rw [h.fr.accessible]; exact hacc, h48⟩, hzw, hzg,
    h.sepOf hzs hh, hne, hzl, hal, h.ext.held hh, h48⟩

end FvModexp.Arm64.NatSqr
