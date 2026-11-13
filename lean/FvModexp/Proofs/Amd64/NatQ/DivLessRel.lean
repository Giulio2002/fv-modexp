import FvModexp.Proofs.Amd64.NatQ.DivRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLessRel.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64), `u < v`: the join after `z2.make(len u)` (`joinS = fn + 0x28a`) and its facts

`q = z[:0]` stored at `SP - 56 … -40`; `RAX = RCX = len u`, `RBX = p`, `RDX = c` (the array of `r`: `z2`'s when
`len u ≤ cap z2`, else fresh). Port of `Arm64/Nat/DivRel.lean`'s `AtS`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

/-- the join of the `z2.make(len u)` paths (`fn + 0x28a`) -/
abbrev joinS : Nat := 0x5ee1aa

structure AtS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc z2 z2c u ul : Nat) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 joinS
  sp : S.regs 4 = s.regs 4 - 232#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  r0 : S.regs 0 = BitVec.ofNat 64 ul
  r1 : S.regs 1 = BitVec.ofNat 64 ul
  r3 : S.regs 3 = BitVec.ofNat 64 p
  r2 : S.regs 2 = BitVec.ofNat 64 c
  arr : (p = z2 ∧ c = z2c ∧ ul ≤ z2c) ∨
    (z2c < ul ∧ ul ≤ c ∧ c ≤ ul + 4 ∧ p % 8 = 0 ∧ p + 8 * c ≤ 2 ^ 48 ∧ InRanges p (8 * c) R.rt ∧
      ApartAll p (8 * c) L ∧ InRanges p (8 * c) L' ∧ S.mem.accessible p (8 * c) true = true)
  ext : LiveExt R L L'
  bud : b - makeCost ul ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' S.mem)
  mf : MemFrame s.mem S.mem (R.rt ++ win s 41512 112)
  lf : LiveFrame s.mem S.mem L []
  reg : S.mem.regions = s.mem.regions
  ra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  q0 : S.mem.readLE ((s.regs 4).toNat - 56) 8 = zp
  q1 : S.mem.readLE ((s.regs 4).toNat - 48) 8 = 0
  q2 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = zc
  s8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = u

/-- window-only frames keep the invariant and the live objects -/
theorem winOnly {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} (hce : CallEnv R L s 41512 112)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) {M : Janus.Arm64.Memory}
    (hF : MemFrame s.mem M (win s 41512 112)) :
    R.inv b L (s.regs 14).toNat (view R.rt L M) ∧ MemFrame s.mem M (R.rt ++ win s 41512 112) ∧
      LiveFrame s.mem M L [] := by
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hce
  simp only [regSP] at hb'
  refine ⟨FvModexp.Amd64.NatAdd.inv_win hF hout hb' hinv, hF.mono fun a n h => by
    simp only [outside_append] at h; exact h.2, ⟨fun a n hin _ => hF.readLE a n ?_⟩⟩
  obtain ⟨r, hr, i1, i2⟩ := hin
  have := hLs r hr
  simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega

end FvModexp.Amd64.Q.NatDiv
