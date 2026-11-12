import FvModexp.Proofs.Arm64.Nat.KSqrPQ

set_option autoImplicit false

/-!
# `karatsubaSqr` (arm64): `kPC`, loop 2 exit → the `stk.nat` call → `KB1` (split out of KSqrPA)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- loop 2 exit (`R5 = len x1`) → the `stk.nat(2·n2 + 1)` call: the `x0`/`x1`/`z0`/`z2` headers, the spills, the
defer record, then `ks_natcall` -/
theorem kPC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {S : State} (hQ : KQ R b L W st zp zc xp n xc s S.mem) {lx0 lx1 : Nat}
    (hl0 : lx0 ≤ kn2 n) (hv0 : natVal s.mem xp lx0 = natVal s.mem xp (kn2 n)) (hn0 : NatNorm s.mem xp lx0)
    (hl1 : lx1 ≤ n - kn2 n)
    (hv1 : natVal s.mem (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n))
    (hn1 : NatNorm s.mem (xp + 8 * kn2 n) lx1)
    (hpc : S.pc = BitVec.ofNat 64 kL2x) (hsp : S.sp = s.sp - 320#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 zp)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 lx1) (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 (n + 1)) (h8 : S.regs 8 = BitVec.ofNat 64 lx0)
    (h9 : S.regs 9 = BitVec.ofNat 64 (kn2 n)) (h10 : S.regs 10 = BitVec.ofNat 64 (xc - kn2 n))
    (h11 : S.regs 11 = BitVec.ofNat 64 (xp + 8 * kn2 n)) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 328#64) (h18 : S.regs 18 = s.regs 18)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (S' : State) (Lk : List (Nat × Nat)) (bk : Nat),
      KB1 R b L W st zp zc xp n xc s lx0 lx1 (stW S'.mem st + 8 * stLen s.mem st) S' Lk bk →
      ReachesRet (LibSqr.program.link impl) ret S' Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  have hpre := hQ.pre
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩, hW, -, -, -, h80, hxc, hxc40, hn12, -, -, hxp48, -, -, hzc,
    hzc40, -, -, -, -, -, -, hsp0, -, -, -, -⟩ := hpre
  have hzl : zp + 8 * zc ≤ 2 ^ 48 := (hQ.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)).2.2.2
  have hsp1 := hsp0
  obtain ⟨hst0, ⟨hst8, -, -, hst48, -⟩, hstw, -⟩ := hsp1
  have hstacc : S.mem.accessible st 24 false = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_sub _ hsp0.2.1.2.2.1 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold ksqrW at hW
  have hk : kn2 n ≤ n ∧ n - kn2 n ≤ kn2 n ∧ 0 < kn2 n ∧ 2 * kn2 n ≤ n + 1 ∧ n ≤ 2 * kn2 n := by
    simp only [kn2]; omega
  have hsacc : S.mem.accessible (s.sp.toNat - 328) 376 true = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : S.mem.accessible (s.sp.toNat - 328) 376 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear hw
  have eL : S.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 :=
    hQ.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hsl1 : BitVec.ofNat 64 (kn2 n) <<< 1 = BitVec.ofNat 64 (2 * kn2 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hand : BitVec.ofNat 64 (n + 1) &&& 18446744073709551614#64 = BitVec.ofNat 64 (2 * kn2 n) := by
    have hsh2 : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kn2 n) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega
    rw [kand2, hsh2, hsl1]
  have hsl4 : BitVec.ofNat 64 (kn2 n) <<< 4 = BitVec.ofNat 64 (16 * kn2 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hz2 : BitVec.ofNat 64 zc - BitVec.ofNat 64 (2 * kn2 n) = BitVec.ofNat 64 (zc - 2 * kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hn2 : BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 (2 * kn2 n) = BitVec.ofNat 64 (2 * n - 2 * kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hm : (BitVec.ofNat 64 (kn2 n) &&& (0#64 - BitVec.ofNat 64 (zc - 2 * kn2 n)).sshiftRight 63) =
      BitVec.ofNat 64 (kn2 n) := by
    rw [BitVec.and_comm]
    exact neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hkt : BitVec.ofNat 64 (2 * kn2 n) + 1#64 = BitVec.ofNat 64 (kT n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kT]; omega
  janus_run [eL, hand, hsl1, hsl4, hz2, hn2, hm, hkt] until [stkNatA]
  refine ks_natcall impl hap R hgr hmc hwb (P := _) (s := s) (lx0 := lx0) (lx1 := lx1)
    { pre := hQ.pre, pc := rfl, sp := ?sp, g := ?g, fpr := ?fpr, r18 := ?r18, r0 := ?r0, r1 := ?r1, r30 := ?r30,
      l0 := hl0, v0 := hv0, nn0 := hn0, l1 := hl1, v1 := hv1, nn1 := hn1, fr := ?fr, reg := ?reg,
      lr := ?lr, fp := ?fp, bit := ?bit, n2s := ?n2s, n1s := ?n1s, dfn := ?dfn, dst := ?dst, dln := ?dln,
      dpt := ?dpt, s1 := ?s1, s2 := ?s2, s3 := ?s3, s4 := ?s4, s5 := ?s5, x0h := ?x0h, x1h := ?x1h,
      z0h := ?z0h, z2h := ?z2h } hK
  case fr => exact hQ.fr.trans (by janus_frame) fun a k h => ⟨h, h⟩
  case reg => simp only [Memory.regions_writeLE]; exact hQ.reg
  all_goals (try simp only [IntAt, Z0H, Z2H])
  all_goals janus_simp
  all_goals first | exact hQ.lr | exact hQ.fp | exact hQ.s5 | exact Nat.mod_eq_of_lt (by omega) | skip
  all_goals (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.NatSqr
