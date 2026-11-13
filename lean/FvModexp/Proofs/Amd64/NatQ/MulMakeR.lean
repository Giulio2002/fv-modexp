import FvModexp.Proofs.Amd64.NatQ.MulRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulMakeR.lean — TIGHT COSTS] `nat.mul` (amd64), `m ≥ n ≥ 2`: `if alias(z, x) || alias(z, y) { z = nil }; z = z.make(m + n)` (natmul.go:31-34) → the join `0x5f09d5`

`make_reuse`: `cap z ≥ m + n` and `z` no alias of `x` / `y` (the cap-end tests `CMPQ R12, DX; JNE` at `0x5f08d6` and
`CMPQ R13, R12; JNE` at `0x5f0920`; the bounds check on `cap y - 1` cannot fire as `cap y ≥ len y ≥ 2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make_reuse (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0840)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hy1 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat) (hy2 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat)
    (hy3 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hyl2 : 2 ≤ yl.toNat) (hyx : yl.toNat ≤ xl.toNat)
    (hz : xl.toNat + yl.toNat ≤ zc.toNat) (hnx : zp.toNat + 8 * zc.toNat ≠ xp.toNat + 8 * xc.toNat)
    (hny : zp.toNat + 8 * zc.toNat ≠ yp.toNat + 8 * yc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc yp yl yc → ReachesRet (LibMul.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s Q := by
  have hpre' := hpre
  obtain ⟨hce, hmw, -, -, -, ⟨⟨hxlc, hxc40, -, -, hxh, -⟩, ⟨hylc, hyc40, -, -, hyh, -⟩,
    ⟨hzc40, hzl, -, -, hzx, hzy⟩, -⟩, -, -, -, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
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
  have hxy := toInt_small (yl + xl) (by rw [BitVec.toNat_add]; omega)
  janus64_run [hy1, hy2, hy3, BitVec.msb_eq_decide, toInt_small zc (by omega), toInt_small xl (by omega),
    toInt_small yl (by omega), hxy] until [0x5f09d5]
  refine hK zp.toNat zc.toNat L b _ (core_reuse hpre hz ?hF) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpx, hpy, hnx, hny⟩
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.Q.NatMul
