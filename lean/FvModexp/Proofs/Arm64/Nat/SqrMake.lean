import FvModexp.Proofs.Arm64.Nat.SqrRel
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.sqr` (arm64), `n ≥ 2`: `if alias(z, x) { z = nil }; z = z.make(2n)` (natmul.go:85-88) → the join `+0x104`

`make_reuse`: `cap z ≥ 2n` and `z` not an alias of `x` (the cap-end test at `+0x84`); `make_alloc`: otherwise,
`makeslice(Word, 2n, 2n + 4)`. Both hand `Core` and `JoinAt` to a continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make_reuse (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : 2 * xl.toNat ≤ zc.toNat) (hna : zp.toNat + 8 * zc.toNat ≠ xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s Q := by
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, hxlc, hxc40, hxl12, -, hxh, -, hzc40, hzl, -, -, hzx, -, -, -, -, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hpx : Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat) := by
    rcases hzx with ⟨e1, e2⟩ | h
    · exact absurd (by rw [e1, e2]) hna
    · exact h (by omega) (by omega)
  obtain ⟨hz8, -, -, hz48⟩ := hzl (by omega)
  obtain ⟨-, hx48⟩ := hxh (by omega)
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega)] until [0x1bb524]
  refine hK zp.toNat zc.toNat L b _ (core_reuse hpre hz ?hF) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hpx, hna⟩
  case hF => simp only [winA]; janus_frame
  all_goals try janus_simp
  all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem make_alloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s Q := by
  have hpre' := hpre
  obtain ⟨hce, hsw, hsv, -, hty, hxlc, hxc40, hxl12, -, hxh, -, hzc40, hzl, -, -, -, -, -, -, hcost, hinv⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxh' := (hxh (by omega)).1
  obtain ⟨-, hx48⟩ := hxh (by omega)
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, 2 * xl.toNat, 2 * xl.toNat + 4] := hsv.1 _ _ _ (by omega)
  have hmc : makeB (2 * xl.toNat) = allocCost (8 * (2 * xl.toNat + 4)) := rfl
  have hmc2 : makeB (2 * xl.toNat) ≤ sqrC (stLen s.mem st.toNat) xl.toNat := by unfold sqrC; omega
  have hbl := blockSize_le_allocCost (8 * (2 * xl.toNat + 4)) true
  have hbs : blockSize (8 * (2 * xl.toNat + 4)) true ≤ b := by omega
  have hwt : Apart NatAdd.wordT 16 (s.sp.toNat - W) (W + 64) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt
  rw [show 2 * xl.toNat = xl.toNat + xl.toNat by omega] at hok1 hbs
  simp only [LiveSep, win] at hLs
  have hzl' : 0 < zc.toNat → zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 := fun h => (hzl h).2.2.2
  clear hzl
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega)] until [0x1bb524] calls [hmk.pos]
  all_goals
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    refine hK ptr.toNat (2 * xl.toNat + 4) _ _ _ (Core.win (core_alloc (c := 2 * xl.toNat + 4) hpre ?hF ?qcs hLF hMF
        hAp hIn hle ?qacc (h8 (Or.inr (by omega))) hinv' ?q1 ?q2 ?q3 ?q4 ?q5 hz) ?hF2)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        apart_of_held (hxh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs1)
          (ApartAll.sub' hAp (Nat.le_refl _) ?qs2), ?qna⟩
    case qna =>
      have := apart_of_held hxh' (hIn.sub (Nat.le_refl _) (n := 8 * (2 * xl.toNat + 4)) (by omega))
        (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
      unfold Apart at this; omega
    case qs1 => omega
    case qs2 => omega
    case hF => simp only [winA]; janus_frame
    case hF2 => simp only [winA]; janus_frame
    case qcs => intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
    case qacc => rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc
    case q1 => omega
    case q2 => rw [hmc, show 2 * xl.toNat + 4 = xl.toNat + xl.toNat + 4 by omega]; exact blockSize_le_allocCost _ true
    case q3 => omega
    case q4 => omega
    case q5 => omega
    all_goals try janus_simp
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega) | assumption

end FvModexp.Arm64.NatSqr
