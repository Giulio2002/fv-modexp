import FvModexp.Proofs.Arm64.Nat.MulRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.mul` (arm64), `m ≥ n ≥ 2`: `if alias(z, x) || alias(z, y) { z = nil }; z = z.make(m + n)` (natmul.go:31-35)
→ the join `0x1baf70`

`make_reuse` (this module; `make_alloc` in MulMakeA): `cap z ≥ m + n` and `z` an alias of neither operand (cap-end tests at `0x1baec4..0x1baf08`);
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

end FvModexp.Arm64.NatMul
