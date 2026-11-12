import FvModexp.Proofs.Arm64.Nat.KSqrPQ

set_option autoImplicit false

/-!
# `karatsubaSqr` (arm64): `kPB`, loop 1 exit → loop 2 head (split out of KSqrPA)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- loop 1 exit (`R8 = len x0`) → loop 2 head (`R5 = n - n2`, base `R11 = xp + 8·n2`, `R10 = xc - n2`) -/
theorem kPB (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {S : State} (hQ : KQ R b L W st zp zc xp n xc s S.mem) {lx0 : Nat} (hl0 : lx0 ≤ kn2 n)
    (hpc : S.pc = BitVec.ofNat 64 kL1x) (hsp : S.sp = s.sp - 320#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 zp)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 n) (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 (n + 1)) (h8 : S.regs 8 = BitVec.ofNat 64 lx0)
    (h9 : S.regs 9 = BitVec.ofNat 64 (kn2 n)) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 328#64)
    (h18 : S.regs 18 = s.regs 18)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S2 : State, S2.pc = BitVec.ofNat 64 kL2 → S2.sp = s.sp - 320#64 →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 1 = BitVec.ofNat 64 zp → S2.regs 2 = BitVec.ofNat 64 (2 * n) →
      S2.regs 3 = BitVec.ofNat 64 zc → S2.regs 4 = BitVec.ofNat 64 xp → S2.regs 5 = BitVec.ofNat 64 (n - kn2 n) →
      S2.regs 6 = BitVec.ofNat 64 xc → S2.regs 7 = BitVec.ofNat 64 (n + 1) → S2.regs 8 = BitVec.ofNat 64 lx0 →
      S2.regs 9 = BitVec.ofNat 64 (kn2 n) → S2.regs 10 = BitVec.ofNat 64 (xc - kn2 n) →
      S2.regs 11 = BitVec.ofNat 64 (xp + 8 * kn2 n) → S2.regs 28 = s.regs 28 →
      S2.regs 29 = s.sp - 328#64 → S2.regs 18 = s.regs 18 → S2.mem = S.mem →
      ReachesRet (LibSqr.program.link impl) ret S2 Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  obtain ⟨-, -, -, -, -, h80, hxc, hxc40, hn12, -, -, hxp48, -⟩ := hQ.pre
  have hk : kn2 n ≤ n ∧ n - kn2 n ≤ kn2 n ∧ 0 < kn2 n := by simp only [kn2]; omega
  have hsh2 : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kn2 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega
  have hs1 : BitVec.ofNat 64 xc - BitVec.ofNat 64 (kn2 n) = BitVec.ofNat 64 (xc - kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hs2 : BitVec.ofNat 64 n - BitVec.ofNat 64 (kn2 n) = BitVec.ofNat 64 (n - kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hm := kmask n xc (by simp only [kn2]; omega) hxc40
  janus_run [hsh2, hm] until [kL2]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus_simp
  all_goals first
    | exact hs1
    | exact hs2
    | (rw [← BitVec.ofNat_add, show xp + kn2 n * 8 = xp + 8 * kn2 n by omega])
    | skip

end FvModexp.Arm64.NatSqr
