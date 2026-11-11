import FvModexp.Proofs.Arm64.Nat.LshDefs

/-!
# `nat.lsh` (arm64): `z.lsh(z, s)` with `s` possibly `0` (nat.go:955) — statement and the `s = 0` path

With `z = x` (same pointer and length, `0 < len x`) and `s = 0`, `same(z, x)` holds and `lsh` returns `z` itself
(`+0x2c … +0x48`: `CMP R1, R4; BNE; CBZ R1; CMP R0, R3; BNE`; `RET`); memory changes only in the window. The post is
`NatOF`-style: the old array, or (when `0 < s`, via `ens`) a fresh one of capacity `≥ n + 1`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (liveFrame_of_memFrame)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh

/-- precondition of `z.lsh(z, s)`: `LshPreA` with `z = x` as slices (pointer and length), `0 < len x`, `x` normalised -/
def PreZ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl sh : Nat) (s : State) : Prop :=
  EvenHyp.LshPreA R b L 4256 64 zp zl zc x xl sh s ∧ zp = x ∧ zl = xl ∧ 0 < xl ∧ NatNorm s.mem x xl

/-- postcondition of `z.lsh(z, s)`: `LshPost` with `NatOF` (old array, or fresh with capacity `≥ need`) -/
@[reducible] def PostZ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      ExpHyp.NatOF R L L' s'.mem zp zc (xl + sh / 64 + 1) p' l' c' (natVal s.mem x xl * 2 ^ sh) ∧
      ExpHyp.RtPost R b (makeCost (xl + sh / 64 + 1)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4256 64 ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- the premise shape for nat.go:955 (`z.lsh(z, s)`, `s` may be `0`) -/
def HypZ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [z, zl, zc, x, xl, xc, sh]
      (fun s => EvenHyp.LshPreA R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s ∧
        z.toNat = x.toNat ∧ zl.toNat = xl.toNat ∧ 0 < xl.toNat ∧ NatNorm s.mem x.toNat xl.toNat)
      (fun s s' => PostZ R b L z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

/-- the post of the `s = 0` return (memory changed only in the window) -/
theorem postZ0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl : Nat} {s : State}
    (hpre : PreZ R b L zp zl zc x xl 0 s)
    {M' : Memory} (hF : MemFrame s.mem M' (winA s 4256 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 1 = BitVec.ofNat 64 zl) (h2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    PostZ R b L zp zc x xl 0 s s' := by
  subst hm
  obtain ⟨⟨⟨_, ⟨_, hb', _, _⟩, _, hout, _, _, hLs, _⟩, _, hzl, ⟨hz40, hzL, _⟩,
    ⟨_, _, _, _, hxw⟩, _, _, _, hinv⟩, hzx, hzlx, hx0, hN⟩ := hpre
  subst hzx hzlx
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 64 ≤ a) → Outside a n (winA s 4256 64) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hv : natVal s'.mem zp zl = natVal s.mem zp zl := hF.readLE _ _ (hFo _ _ (by omega))
  refine ⟨zp, zl, zc, h0, h1, h2, L, b, ⟨by rw [hv, Nat.pow_zero, Nat.mul_one], ?_, hzl, hz40, ?_, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_frame_winA hF hout hb' (by omega) hinv⟩, ?_, ?_⟩
  · rcases hN with h | h
    · exact Or.inl h
    · right; rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact h
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzL hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := winA s 4256 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroSh (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 xl) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 0)
    (hpre : PreZ R b L zp zl zc x xl 0 s) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostZ R b L zp zc x xl 0 s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hn16, -, -, -⟩, hzx, hzlx, hx0, -⟩ := hpre'
  subst hzx hzlx
  have hx0' : (BitVec.ofNat 64 zl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [hx0']
  refine postZ0 hpre ?hF _ rfl ?_ ?_ ?_
  case hF => simp only [winA]; janus_frame
  all_goals janus_simp

end FvModexp.Arm64.Lsh
