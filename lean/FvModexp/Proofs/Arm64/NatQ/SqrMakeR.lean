import FvModexp.Proofs.Arm64.NatQ.SqrRel
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/SqrMakeR.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `n ≥ 2`: `if alias(z, x) { z = nil }; z = z.make(2n)` (natmul.go:85-88) → the join `+0x104`

`make_reuse` (this module): `cap z ≥ 2n` and `z` not an alias of `x` (the cap-end test at `+0x84`); `make_alloc`: otherwise,
`makeslice(Word, 2n, 2n + 4)` (SqrMakeA). Both hand `Core` and `JoinAt` to a continuation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem make_reuse (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : 2 * xl.toNat ≤ zc.toNat) (hna : zp.toNat + 8 * zc.toNat ≠ xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
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

end FvModexp.Arm64.Q.NatSqr
