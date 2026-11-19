import FvModexp.Proofs.Amd64.Nat.LshDefs

/-!
# `nat.lsh` (amd64): `z.lsh(z, s)` with `s` possibly `0` (nat.go:955) — statement and the `s = 0` path

With `z = x` (same pointer and length, `0 < len x`) and `s = 0`, `same(z, x)` holds and `lsh` returns `z` itself
(`TESTQ R9; JNE` not taken; `CMPQ SI, BX; JNE; TESTQ BX; JE; CMPQ DI, AX; JNE` all fall through; `RET`); memory changes
only in the window. The post is `NatOF`-style: the old array, or (when `0 < s`, via `ens`) a fresh one of capacity
`≥ n + 1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (liveFrame_of_memFrame inv_win)
open FvModexp.Amd64.EvenHyp (RtPost)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Lsh

/-- an old-or-fresh result nat (amd64 twin of `Arm64.ExpHyp.NatOF`) -/
@[reducible] def NatOF (R : RtInv) (L L' : List (Nat × Nat)) (m' : Janus.Arm64.Memory) (zp zc need p' l' c' v : Nat) :
    Prop :=
  natVal m' p' l' = v ∧ NatNorm m' p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧ NatLive m' R L' p' c' ∧
    ((p' = zp ∧ c' = zc) ∨ (need ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))

/-- precondition of `z.lsh(z, s)`: `LshPreA` with `z = x` as slices (pointer and length), `0 < len x`, `x` normalised -/
def PreZ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl sh : Nat) (s : State) : Prop :=
  LshPreA R b L 4248 64 zp zl zc x xl sh s ∧ zp = x ∧ zl = xl ∧ 0 < xl ∧ NatNorm s.mem x xl

/-- the result part of `z.lsh(z, s)`'s postcondition: `NatOF` (old array, or fresh with capacity `≥ need`) -/
@[reducible] def ResZ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 3 = BitVec.ofNat 64 l' ∧ s'.regs 1 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (xl + sh / 64 + 1) p' l' c' (natVal s.mem x xl * 2 ^ sh) ∧
      RtPost R b (makeCost (xl + sh / 64 + 1)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- postcondition of `z.lsh(z, s)` (AMD64 DF CONVENTION) -/
@[reducible] def PostZ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ ResZ R b L stk above zp zc x xl sh s s'

/-- internal post (DF in `RegsOK`) -/
@[reducible] def PostZI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ ResZ R b L 4248 64 zp zc x xl sh s s'

/-- the premise shape for nat.go:955 (`z.lsh(z, s)`, `s` may be `0`) -/
def HypZ (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [z, zl, zc, x, xl, xc, sh]
      (fun s => LshPreA R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s ∧
        z.toNat = x.toNat ∧ zl.toNat = xl.toNat ∧ 0 < xl.toNat ∧ NatNorm s.mem x.toNat xl.toNat)
      (fun s s' => PostZ R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

/-- `PostI` gives `PostZI` -/
theorem postI_postZI {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s s' : State}
    (h : PostI R b L zp zc x xl sh s s') : PostZI R b L zp zc x xl sh s s' := by
  obtain ⟨hfs, p', l', c', h0, h1, h2, L', b', ⟨hv, hn, hl, hc, hlive, hru, hfr⟩, hneed, hrt, hmf, hlf⟩ := h
  refine ⟨hfs, p', l', c', h0, h1, h2, L', b', ⟨hv, hn, hl, hc, hlive, ?_⟩, hrt, hmf, hlf⟩
  by_cases hz : xl + sh / 64 + 1 ≤ zc
  · exact Or.inl (hru hz)
  · have hk := hneed (by omega)
    exact Or.inr ⟨hk, hfr (by omega) (by omega)⟩

/-- the post of the `s = 0` return (memory changed only in the window) -/
theorem postZ0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl : Nat} {s : State}
    (hpre : PreZ R b L zp zl zc x xl 0 s)
    {M' : Janus.Arm64.Memory} (hF : MemFrame s.mem M' (win s 4248 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 zl) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (hfs : s'.fsBase = s.fsBase) :
    PostZI R b L zp zc x xl 0 s s' := by
  subst hm
  obtain ⟨⟨⟨_, ⟨hb', _, _⟩, _, _, hout, _, _, hLs, _⟩, _, hzl, ⟨hz40, hzL, _⟩,
    ⟨_, _, _, _, hxw⟩, _, _, _, hinv⟩, hzx, hzlx, hx0, hN⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hb'
  subst hzx hzlx
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 64 ≤ a) → Outside a n (win s 4248 64) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hv : natVal s'.mem zp zl = natVal s.mem zp zl := hF.readLE _ _ (hFo _ _ (by omega))
  refine ⟨hfs, zp, zl, zc, h0, h1, h2, L, b, ⟨by rw [hv, Nat.pow_zero, Nat.mul_one], ?_, hzl, hz40, ?_,
    Or.inl ⟨rfl, rfl⟩⟩, ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_win hF hout hb' hinv⟩, ?_, ?_⟩
  · rcases hN with h | h
    · exact Or.inl h
    · right; rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact h
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzL hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := win s 4248 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroSh (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc 0) (hpre : PreZ R b L zp zl zc x xl 0 s) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostZI R b L zp zc x xl 0 s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    ⟨hx40, -, -, -, -⟩, hn16, -, -, -⟩, hzx, hzlx, hx0, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  subst hzx hzlx
  have hx0' : (BitVec.ofNat 64 zl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hx0', BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, postZ0 hpre ?hF _ rfl ?_ ?_ ?_ ?_⟩
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Lsh
