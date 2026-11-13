import FvModexp.Proofs.Amd64.NatQ.KSqrPQ

set_option autoImplicit false

/-!
# [amd64 port (divmc s40) of the Q-form Arm64/NatQ/KSqrPC.lean — TIGHT COSTS] `karatsubaSqr` (amd64): loop 2 exit →
the `stk.nat(2·n2 + 1)` call (natmul.go:286-292)

`kPC`: `0x5f2454` (`R8 = len x1`) → `(*stack).nat`'s entry: the `x[n2:]` bound (panic refuted), the `x0`/`x1` headers
(`RSP - 48` / `RSP - 80`), `R10 = 2·n2` (`ANDQ $-2`) with the `z[:2n2]` / `z[2n2:]` bounds (panics refuted), the `z0`
header (`RSP - 112`), the spills `RSP + 8..+40`, `n2` at `RSP - 248`, the `z2` header (`RSP - 144`), the defer record
(`RSP - 168..-152`, its address at `RSP - 16`), defer bit `:= 1`, `CALL` (return `0x5f2578` at `RSP - 320`); then
`ks_natcall`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kPC (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {S : State} (hQ : KQ R b H L W st zp zc xp n xc s S.mem)
    (hn1s : S.mem.readLE ((s.regs 4).toNat - 240) 8 = 8 * kn2 n) {lx0 lx1 : Nat}
    (hl0 : lx0 ≤ kn2 n) (hv0 : natVal s.mem xp lx0 = natVal s.mem xp (kn2 n)) (hn0 : NatNorm s.mem xp lx0)
    (hl1 : lx1 ≤ n - kn2 n)
    (hv1 : natVal s.mem (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n))
    (hn1 : NatNorm s.mem (xp + 8 * kn2 n) lx1) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (hpc : S.rip = BitVec.ofNat 64 kL2x) (hsp : S.regs 4 = s.regs 4 - 312#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 zp)
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : S.regs 7 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 lx1)
    (h9 : S.regs 9 = BitVec.ofNat 64 (xp + 8 * kn2 n)) (h10 : S.regs 10 = BitVec.ofNat 64 (n + 1))
    (h11 : S.regs 11 = BitVec.ofNat 64 (8 * kn2 n)) (h12 : S.regs 12 = BitVec.ofNat 64 xc)
    (h13 : S.regs 13 = BitVec.ofNat 64 (kn2 n)) (h15 : S.regs 15 = BitVec.ofNat 64 (xc - kn2 n))
    (h2 : S.regs 2 = BitVec.ofNat 64 lx0) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx : S.xmm 15 = s.xmm 15)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (S' : State) (Lk : List (Nat × Nat)) (bk : Nat),
      KB1 R b H L W st zp zc xp n xc s lx0 lx1 (stW S'.mem st + 8 * stLen s.mem st) S' Lk bk →
      ReachesRet (LibSqr.program.link impl) ret S' Q) :
    ReachesRet (LibSqr.program.link impl) ret S Q := by
  have hpre := hQ.pre
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, hal, -⟩, hW, -, -, -, h80, hxc, hxc40, hn12, -, -, hxp48, -, -, hzc,
    hzc40, hzl, -, -, -, -, -, -, hsp0, -⟩ := hpre
  simp only [regSP] at hb' ha hw
  have hzl' : zp + 8 * zc ≤ 2 ^ 48 := (hzl (by omega)).2.2.2
  clear hzl
  obtain ⟨-, ⟨-, -, hstacc0, hst48, -⟩, hstw, -⟩ := hsp0
  have hstacc : S.mem.accessible (st + 8) 8 false = true := by
    rw [hQ.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _
      (Janus.Arm64.Memory.accessible_sub _ hstacc0 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)) (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold ksqrW at hW
  have hk : kn2 n ≤ n ∧ n - kn2 n ≤ kn2 n ∧ 0 < kn2 n ∧ 2 * kn2 n ≤ n + 1 ∧ n ≤ 2 * kn2 n := by
    simp only [kn2]; omega
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have eL : S.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 :=
    hQ.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hand : BitVec.ofNat 64 (n + 1) &&& 18446744073709551614#64 = BitVec.ofNat 64 (2 * kn2 n) := by
    rw [kand2, kshr1 (by omega), kshl1 (by omega)]
  have hsl4 := kshl4 (a := kn2 n) (by omega)
  have hz2 : BitVec.ofNat 64 zc - BitVec.ofNat 64 (2 * kn2 n) = BitVec.ofNat 64 (zc - 2 * kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hn2 : BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 (2 * kn2 n) = BitVec.ofNat 64 (2 * n - 2 * kn2 n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hm := kmask (zc - 2 * kn2 n) (16 * kn2 n) (by omega) (by omega)
  have hm' := kmask' (zc - 2 * kn2 n) (16 * kn2 n) (by omega) (by omega)
  have hza : BitVec.ofNat 64 zp + BitVec.ofNat 64 (16 * kn2 n) = BitVec.ofNat 64 (zp + 16 * kn2 n) :=
    bv_add_ofNat (by omega)
  have hdd : BitVec.ofNat 64 (kn2 n) + BitVec.ofNat 64 (kn2 n) = BitVec.ofNat 64 (2 * kn2 n) :=
    by rw [bv_add_ofNat (by omega)]; congr 1; omega
  have hkt : BitVec.ofNat 64 (2 * kn2 n) + 1#64 = BitVec.ofNat 64 (kT n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kT]; omega
  have hkt' : BitVec.ofNat 64 (2 * kn2 n) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (kT n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kT]; omega
  have esp : (s.regs 4 - 312#64).toNat = (s.regs 4).toNat - 312 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [eL, hand, hsl4, hz2, hn2, hm, hm', hza, hdd, hkt, hkt', esp, BitVec.msb_eq_decide] until [stkNatA]
  refine ks_natcall impl hap R hgr hmc hwb (P := _) (s := s) (lx0 := lx0) (lx1 := lx1)
    { pre := hQ.pre, pc := ?pc, sp := ?sp, g := ?g, fpr := ?fpr, fs := ?fs, df := ?df, x15 := ?x15, r0 := ?r0,
      r1 := ?r1, ra := ?ra, l0 := hl0, v0 := hv0, nn0 := hn0, l1 := hl1, v1 := hv1, nn1 := hn1, fr := ?fr,
      reg := ?reg, fp := ?fp, bit := ?bit, n2s := ?n2s, n1s := ?n1s, dfn := ?dfn, dst := ?dst, dln := ?dln,
      dpt := ?dpt, s1 := ?s1, s2 := ?s2, s3 := ?s3, s4 := ?s4, s5 := ?s5, x0h := ?x0h, x1h := ?x1h,
      z0h := ?z0h, z2h := ?z2h } hx150 hdf0 hK
  case fr => exact hQ.fr.trans (by janus_frame) fun a k h => ⟨h, h⟩
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hQ.reg
  case fp => janus64_simp; exact hQ.fp
  case s5 => janus64_simp; exact hQ.s5
  case n1s => janus64_simp
  all_goals (try simp only [IntAt, Z0H, Z2H])
  all_goals janus64_simp
  all_goals first
    | exact Nat.mod_eq_of_lt (by omega)
    | exact hfs
    | exact hdf
    | exact hx
    | exact h14
    | skip
  all_goals (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.Q.NatSqr
