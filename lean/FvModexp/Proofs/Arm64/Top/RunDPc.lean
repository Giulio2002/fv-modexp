import FvModexp.Proofs.Arm64.Top.RunDRel
import FvModexp.Proofs.Arm64.Top.RunGS

/-! # `Run` (arm64): program points and join-point relations of the operand segments `D1`..`D3`

Shared by the independent segment modules (`RunD1`, `RunD2`, `RunD2J`, `RunD3`, `RunD3J`, …), so that they do not import
each other (they compile in parallel; docs/history/PERF-log.md "agent top s18"). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcD1 : Nat := segAddr Extracted.program fn + 0x534
abbrev pcD2 : Nat := segAddr Extracted.program fn + 0x65c
abbrev pcD3 : Nat := segAddr Extracted.program fn + 0x760

abbrev pcJ2 : Nat := segAddr Extracted.program fn + 0x624

/-- The state at `J2`. -/
def JoinD2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret : Nat)
    (Lk : List (Nat × Nat)) (bk B : Nat) (U : State) : Prop :=
  U.sp = s.sp - 624#64 ∧ U.regs 28 = s.regs 28 ∧ U.regs 29 = s.sp - 632#64 ∧ U.regs 18 = s.regs 18 ∧
  U.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ U.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  U.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ U.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  U.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ U.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  U.mem.readLE (s.sp.toNat - 520) 8 = hdrV s p len 0 ∧ U.mem.readLE (s.sp.toNat - 528) 8 = hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ U.mem.readLE (s.sp.toNat - 480) 8 = len.toNat - 96 ∧
  U.mem.readLE (s.sp.toNat - 472) 8 = cp.toNat - inOff len ∧ U.mem.readLE (s.sp.toNat - 216) 8 = p.toNat + inOff len ∧
  U.mem.readLE (s.sp.toNat - 504) 8 = min (hdrV s p len 0) (len.toNat - 96) ∧
  U.mem.readLE (s.sp.toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 160) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 152) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 144) 8 = 0 ∧
  hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024 ∧ ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) ∧
  (U.regs 0).toNat = B ∧ (U.regs 1).toNat = hdrV s p len 1 ∧ (U.regs 7).toNat = hdrV s p len 1 ∧
  hdrV s p len 1 ≤ (U.regs 2).toNat ∧
  B + hdrV s p len 1 ≤ 2 ^ 48 ∧ s.mem.accessible B (hdrV s p len 1) false = true ∧ Held R Lk B (hdrV s p len 1) ∧
  (B + hdrV s p len 1 ≤ s.sp.toNat - 624 - 4160 ∨ (s.sp.toNat - 424 ≤ B ∧ B + hdrV s p len 1 ≤ s.sp.toNat - 392) ∨
    s.sp.toNat + 40 ≤ B) ∧
  (∀ j, j < hdrV s p len 1 →
    (U.mem.bytes (B + j)).toNat = padByte s.mem p.toNat len.toNat (96 + hdrV s p len 0 + j)) ∧
  Extracted.program.DataLoaded U.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → U.mem.readLE a n = s.mem.readLE a n) ∧
  U.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + dCost + allocCost 1024) ≤ bk ∧
  R.inv bk Lk (s.regs 28).toNat (view R.rt Lk U.mem) ∧ LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem U.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem U.mem L [] ∧ OpDone R U.mem s p len L Lk 0


abbrev pcJ3 : Nat := segAddr Extracted.program fn + 0x730

/-- The state at `J3`. -/
def JoinD3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret : Nat)
    (Lk : List (Nat × Nat)) (bk B : Nat) (U : State) : Prop :=
  U.sp = s.sp - 624#64 ∧ U.regs 28 = s.regs 28 ∧ U.regs 29 = s.sp - 632#64 ∧ U.regs 18 = s.regs 18 ∧
  U.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ U.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  U.mem.readLE (s.sp.toNat + 8) 8 = c.toNat ∧ U.mem.readLE (s.sp.toNat + 16) 8 = p.toNat ∧
  U.mem.readLE (s.sp.toNat + 24) 8 = len.toNat ∧ U.mem.readLE (s.sp.toNat + 32) 8 = cp.toNat ∧
  U.mem.readLE (s.sp.toNat - 520) 8 = hdrV s p len 0 ∧ U.mem.readLE (s.sp.toNat - 528) 8 = hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ U.mem.readLE (s.sp.toNat - 480) 8 = len.toNat - 96 ∧
  U.mem.readLE (s.sp.toNat - 472) 8 = cp.toNat - inOff len ∧ U.mem.readLE (s.sp.toNat - 216) 8 = p.toNat + inOff len ∧
  U.mem.readLE (s.sp.toNat - 504) 8 = min (hdrV s p len 0) (len.toNat - 96) ∧
  U.mem.readLE (s.sp.toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1 ∧
  U.mem.readLE (s.sp.toNat - 552) 8 = hdrV s p len 1 + hdrV s p len 0 ∧
  U.mem.readLE (s.sp.toNat - 192) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 184) 8 = 0 ∧ U.mem.readLE (s.sp.toNat - 176) 8 = 0 ∧
  hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024 ∧ ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) ∧
  (U.regs 0).toNat = B ∧ (U.regs 2).toNat = hdrV s p len 2 ∧
  B + hdrV s p len 2 ≤ 2 ^ 48 ∧ s.mem.accessible B (hdrV s p len 2) false = true ∧ Held R Lk B (hdrV s p len 2) ∧
  (B + hdrV s p len 2 ≤ s.sp.toNat - 624 - 4160 ∨ (s.sp.toNat - 456 ≤ B ∧ B + hdrV s p len 2 ≤ s.sp.toNat - 424) ∨
    s.sp.toNat + 40 ≤ B) ∧
  (∀ j, j < hdrV s p len 2 →
    (U.mem.bytes (B + j)).toNat = padByte s.mem p.toNat len.toNat (96 + (hdrV s p len 0 + hdrV s p len 1) + j)) ∧
  Extracted.program.DataLoaded U.mem ∧
  (∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → U.mem.readLE a n = s.mem.readLE a n) ∧
  U.mem.readLE c.toNat 3 = s.mem.readLE c.toNat 3 ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + 2 * dCost + allocCost 1024) ≤ bk ∧
  R.inv bk Lk (s.regs 28).toNat (view R.rt Lk U.mem) ∧ LiveSep Lk (win s stk 40) ∧
  MemFrame s.mem U.mem (R.rt ++ winA s stk 40) ∧ LiveFrame s.mem U.mem L [] ∧ OpDone R U.mem s p len L Lk 0 ∧
  OpDone R U.mem s p len L Lk 1 ∧ OpsApart U.mem s 2


/-- The budget after the modulus operand's `setBytes` (the join path spent the `RightPadBytes` buffer already). -/
theorem bud_d3join {b bk b2 mc : Nat} (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (hbud : b - (3 * makeCost 4 + 2 * dCost + allocCost 1024) ≤ bk) (hMC0 : mc ≤ allocCost (8 * 132))
    (hb2 : bk - mc ≤ b2) : b - (3 * makeCost 4 + 3 * dCost) ≤ b2 := by
  simp only [dCost] at hbudD hbud ⊢; omega

/-- The budget after operand `k + 1`'s `setBytes` on the direct path (`RelD … k` to `RelD … (k+1)`). -/
theorem bud_dk {b b1 b2 mc : Nat} (k : Nat) (hbud : b - (3 * makeCost 4 + k * dCost) ≤ b1)
    (hMC0 : mc ≤ allocCost (8 * 132)) (hb2 : b1 - mc ≤ b2) : b - (3 * makeCost 4 + (k + 1) * dCost) ≤ b2 := by
  have hd : mc ≤ dCost := by simp only [dCost]; omega
  rw [Nat.add_mul, Nat.one_mul]; omega

/-- The budget after the exponent operand's `setBytes` from the join point `J2`. -/
theorem bud_d2join {b bk b2 mc : Nat} (hbud : b - (3 * makeCost 4 + dCost + allocCost 1024) ≤ bk)
    (hMC0 : mc ≤ allocCost (8 * 132)) (hb2 : bk - mc ≤ b2) : b - (3 * makeCost 4 + 2 * dCost) ≤ b2 := by
  simp only [dCost] at hbud ⊢; omega

end FvModexp.Arm64.Run
