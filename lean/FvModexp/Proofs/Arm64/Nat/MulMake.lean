import FvModexp.Proofs.Arm64.Nat.MulRel
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.mul` (arm64), `m ≥ n ≥ 2`: `if alias(z, x) || alias(z, y) { z = nil }; z = z.make(m + n)` (natmul.go:31-35)
→ the join `0x1baf70`

`make_reuse`: `cap z ≥ m + n` and `z` an alias of neither operand (cap-end tests at `0x1baec4..0x1baf08`);
`make_alloc`: otherwise, `makeslice(Word, m + n, m + n + 4)`. Both hand `Core` and `JoinAt` to a continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (apart_of_held)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make_reuse (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : xl.toNat + yl.toNat ≤ zc.toNat) (hnx : zp.toNat + 8 * zc.toNat ≠ xp.toNat + 8 * xc.toNat)
    (hny : zp.toNat + 8 * zc.toNat ≠ yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s Q := by
  have hpre' := hpre
  obtain ⟨hce, hmw, -, -, -, ⟨⟨hxlc, hxc40, -, -, hxh, -⟩, ⟨hylc, hyc40, -, -, hyh, -⟩,
    ⟨hzc40, hzl, -, -, hzx, hzy⟩, -⟩, -, -, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hpx : Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat) := by
    rcases hzx with ⟨e1, e2⟩ | h
    · exact absurd (by rw [e1, e2]) hnx
    · exact h (by omega) (by omega)
  have hpy : Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat) := by
    rcases hzy with ⟨e1, e2⟩ | h
    · exact absurd (by rw [e1, e2]) hny
    · exact h (by omega) (by omega)
  obtain ⟨hz8, -, -, hz48⟩ := hzl (by omega)
  obtain ⟨-, hx48⟩ := hxh (by omega)
  obtain ⟨-, hy48⟩ := hyh (by omega)
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega), toInt_small yl (by omega)] until [0x1baf70]
  refine hK zp.toNat zc.toNat L b _ (core_reuse hpre hz ?hF) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpx, hpy, hnx, hny⟩
  case hF => simp only [winA]; janus_frame
  all_goals try janus_simp
  all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem make_alloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMul.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : zc.toNat < xl.toNat + yl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat ∨
      zp.toNat + 8 * zc.toNat = yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s Q := by
  have hpre' := hpre
  obtain ⟨hce, hmw, hsv, -, hty, ⟨⟨hxlc, hxc40, hxl12, -, hxh, -⟩, ⟨hylc, hyc40, hyl12, -, hyh, -⟩,
    ⟨hzc40, hzl, -, -, -, -⟩, -⟩, -, hcost, hinv⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := hce
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hxh' := (hxh (by omega)).1
  obtain ⟨-, hx48⟩ := hxh (by omega)
  have hyh' := (hyh (by omega)).1
  obtain ⟨-, hy48⟩ := hyh (by omega)
  have hok1 : R.ok (cA "runtime.makeslice") [NatAdd.wordT, xl.toNat + yl.toNat, xl.toNat + yl.toNat + 4] :=
    hsv.1 _ _ _ (by omega)
  have hmc : makeB (xl.toNat + yl.toNat) = allocCost (8 * (xl.toNat + yl.toNat + 4)) := rfl
  have hmc2 : makeB (xl.toNat + yl.toNat) ≤ mulC (stLen s.mem st.toNat) xl.toNat yl.toNat := by
    unfold mulC; rw [Nat.max_eq_left hyx, Nat.min_eq_right hyx]; exact MC_basic hy2
  have hbl := blockSize_le_allocCost (8 * (xl.toNat + yl.toNat + 4)) true
  have hbs : blockSize (8 * (xl.toNat + yl.toNat + 4)) true ≤ b := by omega
  have hwt : Apart NatAdd.wordT 16 (s.sp.toNat - W) (W + 88) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : NatAdd.wordT
  rw [h_t] at hty hok1 hwt
  rw [Nat.add_comm xl.toNat yl.toNat] at hok1 hbs
  simp only [LiveSep, win] at hLs
  have hzl' : 0 < zc.toNat → zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 := fun h => (hzl h).2.2.2
  clear hzl
  janus_run [toInt_small zc (by omega), toInt_small xl (by omega), toInt_small yl (by omega)] until [0x1baf70]
    calls [hmk.pos]
  all_goals
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hrb _ hinv' _ _
    refine hK ptr.toNat (xl.toNat + yl.toNat + 4) _ _ _ (Core.win (core_alloc (c := xl.toNat + yl.toNat + 4) hpre ?hF
        ?qcs hLF hMF hAp hIn hle ?qacc (h8 (Or.inr (by omega))) hinv' ?q1 ?q2 ?q3 ?q4 ?q5 hz) ?hF2)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        apart_of_held (hxh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs1)
          (ApartAll.sub' hAp (Nat.le_refl _) ?qs2),
        apart_of_held (hyh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs3)
          (ApartAll.sub' hAp (Nat.le_refl _) ?qs4), ?qnx, ?qny⟩
    case qnx =>
      have := apart_of_held hxh' (hIn.sub (Nat.le_refl _) (n := 8 * (xl.toNat + yl.toNat + 4)) (by omega))
        (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
      unfold Apart at this; omega
    case qny =>
      have := apart_of_held hyh' (hIn.sub (Nat.le_refl _) (n := 8 * (xl.toNat + yl.toNat + 4)) (by omega))
        (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
      unfold Apart at this; omega
    case qs1 => omega
    case qs2 => omega
    case qs3 => omega
    case qs4 => omega
    case hF => simp only [winA]; janus_frame
    case hF2 => simp only [winA]; janus_frame
    case qcs => intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
    case qacc => rw [hMF.accessible]; simpa only [Memory.accessible_writeLE] using hacc
    case q1 => omega
    case q2 => rw [hmc]; exact blockSize_le_allocCost _ true
    case q3 => omega
    case q4 => omega
    case q5 => omega
    all_goals try janus_simp
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega) | assumption

end FvModexp.Arm64.NatMul
