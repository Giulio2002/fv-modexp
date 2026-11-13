import Extracted
import FvModexp.Proofs.Amd64.RG.SbA
import FvModexp.Proofs.Amd64.RG.SbH
import FvModexp.Proofs.Amd64.RG.SbB
import FvModexp.Proofs.Amd64.RG.SbC
import FvModexp.Proofs.Amd64.RG.SbD
import FvModexp.Proofs.Amd64.RG.SbE
import FvModexp.Proofs.Amd64.RG.SbF
import FvModexp.Proofs.Amd64.RG.SbG

/-! `(*uint256.Int).SetBytes` for every length `≤ 32` (amd64): the 33 per-length summaries combined. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

theorem sb : Summary Extracted.program sbA (fun s => SbPre (s.regs 1).toNat s ∧ (s.regs 1).toNat ≤ 32)
    (fun s s' => SbPost (s.regs 1).toNat s s') := by
  intro s hpc ⟨hpre, hle⟩
  show ReachesRet _ _ s (SbPost (s.regs 1).toNat s)
  obtain h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 : (s.regs 1).toNat = 0 ∨ (s.regs 1).toNat = 1 ∨ (s.regs 1).toNat = 2 ∨ (s.regs 1).toNat = 3 ∨ (s.regs 1).toNat = 4 ∨ (s.regs 1).toNat = 5 ∨ (s.regs 1).toNat = 6 ∨ (s.regs 1).toNat = 7 ∨ (s.regs 1).toNat = 8 ∨ (s.regs 1).toNat = 9 ∨ (s.regs 1).toNat = 10 ∨ (s.regs 1).toNat = 11 ∨ (s.regs 1).toNat = 12 ∨ (s.regs 1).toNat = 13 ∨ (s.regs 1).toNat = 14 ∨ (s.regs 1).toNat = 15 ∨ (s.regs 1).toNat = 16 ∨ (s.regs 1).toNat = 17 ∨ (s.regs 1).toNat = 18 ∨ (s.regs 1).toNat = 19 ∨ (s.regs 1).toNat = 20 ∨ (s.regs 1).toNat = 21 ∨ (s.regs 1).toNat = 22 ∨ (s.regs 1).toNat = 23 ∨ (s.regs 1).toNat = 24 ∨ (s.regs 1).toNat = 25 ∨ (s.regs 1).toNat = 26 ∨ (s.regs 1).toNat = 27 ∨ (s.regs 1).toNat = 28 ∨ (s.regs 1).toNat = 29 ∨ (s.regs 1).toNat = 30 ∨ (s.regs 1).toNat = 31 ∨ (s.regs 1).toNat = 32 := by omega
  · rw [h0] at hpre ⊢; exact sb0 s hpc hpre
  · rw [h1] at hpre ⊢; exact sb1 s hpc hpre
  · rw [h2] at hpre ⊢; exact sb2 s hpc hpre
  · rw [h3] at hpre ⊢; exact sb3 s hpc hpre
  · rw [h4] at hpre ⊢; exact sb4 s hpc hpre
  · rw [h5] at hpre ⊢; exact sb5 s hpc hpre
  · rw [h6] at hpre ⊢; exact sb6 s hpc hpre
  · rw [h7] at hpre ⊢; exact sb7 s hpc hpre
  · rw [h8] at hpre ⊢; exact sb8 s hpc hpre
  · rw [h9] at hpre ⊢; exact sb9 s hpc hpre
  · rw [h10] at hpre ⊢; exact sb10 s hpc hpre
  · rw [h11] at hpre ⊢; exact sb11 s hpc hpre
  · rw [h12] at hpre ⊢; exact sb12 s hpc hpre
  · rw [h13] at hpre ⊢; exact sb13 s hpc hpre
  · rw [h14] at hpre ⊢; exact sb14 s hpc hpre
  · rw [h15] at hpre ⊢; exact sb15 s hpc hpre
  · rw [h16] at hpre ⊢; exact sb16 s hpc hpre
  · rw [h17] at hpre ⊢; exact sb17 s hpc hpre
  · rw [h18] at hpre ⊢; exact sb18 s hpc hpre
  · rw [h19] at hpre ⊢; exact sb19 s hpc hpre
  · rw [h20] at hpre ⊢; exact sb20 s hpc hpre
  · rw [h21] at hpre ⊢; exact sb21 s hpc hpre
  · rw [h22] at hpre ⊢; exact sb22 s hpc hpre
  · rw [h23] at hpre ⊢; exact sb23 s hpc hpre
  · rw [h24] at hpre ⊢; exact sb24 s hpc hpre
  · rw [h25] at hpre ⊢; exact sb25 s hpc hpre
  · rw [h26] at hpre ⊢; exact sb26 s hpc hpre
  · rw [h27] at hpre ⊢; exact sb27 s hpc hpre
  · rw [h28] at hpre ⊢; exact sb28 s hpc hpre
  · rw [h29] at hpre ⊢; exact sb29 s hpc hpre
  · rw [h30] at hpre ⊢; exact sb30 s hpc hpre
  · rw [h31] at hpre ⊢; exact sb31 s hpc hpre
  · rw [h32] at hpre ⊢; exact sb32 s hpc hpre

end FvModexp.Amd64.RG
