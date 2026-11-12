import FvModexp.Proofs.Amd64.Nat.SqrRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.sqr` (amd64), `n ≥ 2`: `if alias(z, x) { z = nil }; z = z.make(2n)` (natmul.go:85-88) → the join `0x5f1140`

`make_reuse` (this module): `cap z ≥ 2n` and `z` not an alias of `x` (the cap-end test `CMPQ DX, R12; JNE` at
`0x5f10b1`; the bounds check on `cap x - 1` cannot fire as `cap x ≥ len x ≥ 2`); `make_alloc`: otherwise,
`makeslice(Word, 2n, 2n + 4)` (SqrMakeA). Both hand `Core` and `JoinAt` to a continuation. Twin of the arm64 module.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make_reuse (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0fe0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : SPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : 2 * xl.toNat ≤ zc.toNat) (hna : zp.toNat + 8 * zc.toNat ≠ xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) s Q := by
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, hxlc, hxc40, hxl12, -, hxh, -, hzc40, hzl, -, -, hzx, -, -, -, -, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hpx : Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat) := by
    rcases hzx with ⟨e1, e2⟩ | h
    · exact absurd (by rw [e1, e2]) hna
    · exact h (by omega) (by omega)
  obtain ⟨hz8, -, -, hz48⟩ := hzl (by omega)
  obtain ⟨-, hx48⟩ := hxh (by omega)
  have hxx := toInt_small (xl + xl) (by rw [BitVec.toNat_add]; omega)
  janus64_run [BitVec.msb_eq_decide, toInt_small zc (by omega), toInt_small xl (by omega), hxx] until [0x5f1140]
  refine hK zp.toNat zc.toNat L b _ (core_reuse hpre hz ?hF) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hpx, hna⟩
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | omega | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.NatSqr
