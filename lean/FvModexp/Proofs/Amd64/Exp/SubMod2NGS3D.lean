import FvModexp.Proofs.Amd64.Exp.SubMod2NGC

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: the operand facts of the `cmp` / `sub` segment (agent infra s48)

`y'` (`p2, l2`) carries its pointer facts only when non-empty (`Y2`, the shape of `J2G`'s last premise); `x'` (`zp, l1`,
in `z`'s array) gets its facts from the runtime facts `Rt` (`z` live when `0 < cap z`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.EvenHyp

/-- `y'`'s pointer facts at memory `M` (only when non-empty) -/
@[reducible] def Y2 (R : RtInv) (L2 : List (Nat × Nat)) (M : Memory) (s : State) (zp zc p2 l2 : Nat) : Prop :=
  0 < l2 → M.accessible p2 (8 * l2) false = true ∧ p2 + 8 * l2 ≤ 2 ^ 48 ∧ Held R L2 p2 (8 * l2) ∧
    (p2 + 8 * l2 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ p2) ∧ (0 < zc → Apart zp (8 * zc) p2 (8 * l2))

theorem Y2.frame {R : RtInv} {L2 : List (Nat × Nat)} {M M' : Memory} {s : State} {zp zc p2 l2 : Nat}
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (h : Y2 R L2 M s zp zc p2 l2) : Y2 R L2 M' s zp zc p2 l2 :=
  fun hl => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := h hl
    exact ⟨by rw [hF.accessible]; exact a1, a2, a3, a4, a5⟩

/-- a possibly empty nat outside a frame keeps its value and normal form -/
theorem nat_frame0 {M M' : Memory} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) {p l : Nat}
    (hout : 0 < l → Outside p (8 * l) ws) : natVal M' p l = natVal M p l ∧ (NatNorm M p l → NatNorm M' p l) := by
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h; exact ⟨by simp [natVal], fun _ => Or.inl rfl⟩
  · exact ⟨natVal_frame hF (hout h), natNorm_frame hF (hout h)⟩

/-- `x'` in `z`'s array: its facts from the runtime facts (`0 < l1 ≤ cap z`) -/
theorem x1_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L2 : List (Nat × Nat)} {b2 k l1 : Nat}
    (hrt : Rt R bb L s zp zc n k M L2 b2) (hlc1 : l1 ≤ zc) :
    0 < l1 → M.accessible zp (8 * l1) false = true ∧ zp + 8 * l1 ≤ 2 ^ 48 ∧ Held R L2 zp (8 * l1) ∧
      (zp + 8 * l1 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ zp) := fun h => by
  obtain ⟨-, hzh, hza, hz48⟩ := hrt.2.2.2.2.2.2 (by omega)
  have hzw := hpre.zwin.1
  exact ⟨Janus.Arm64.Memory.accessible_sub _ hza (Or.inr rfl) (Nat.le_refl _) (by omega), by omega,
    hzh.sub (Nat.le_refl _) (by omega), by omega⟩

end FvModexp.Amd64.SubMod2N
