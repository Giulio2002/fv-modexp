import FvModexp.Proofs.Arm64.Nat.KSqrProD
import FvModexp.Proofs.Arm64.Nat.KSqrLoop

/-!
# `karatsubaSqr` (arm64): the prologue up to the first inlined `norm` loop (natmul.go:257-283)

`KQ … s M`: the facts of the prologue's memory `M` (frame record, the spill `SP + 40 := xp`, only our frame written).
`kPA`: entry (`0x1bc2b0`) → loop 1 head (`kL1 = 0x1bc324`): stack-guard check (refuted morestack), frame (`SP' = SP - 320`,
`X29`/`X30` at `SP - 328`/`SP - 320`), spills `SP + 16 := zp`, `SP + 40 := xp`, `SP - 16 := 0`, defer bit `:= 0`,
`len z = 2n` (panic refuted), `n ≥ karatsubaSqrThreshold = 80` (the `basicSqr` fallback refuted), `R7 = n + 1`,
`R8 = R9 = n2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- `LSR $1` as Janus spells it (copied from agent expmc's `Exp/W2ZcDefs.lsr1`) -/
theorem klsr1 (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (9223372036854775807#64)[i] = decide (i < 63) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 63
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

/-- the prologue memory facts (see the module doc) -/
structure KQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State) (M : Memory) :
    Prop where
  pre : KPre R b L W st zp (2 * n) zc xp n xc s
  fr : MemFrame s.mem M [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)]
  reg : M.regions = s.mem.regions
  lr : M.readLE (s.sp.toNat - 320) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 328) 8 = (s.regs 29).toNat
  s5 : M.readLE (s.sp.toNat + 40) 8 = xp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kPA (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} (hpre : KPre R b L W st zp (2 * n) zc xp n xc s) (hpc : s.pc = BitVec.ofNat 64 0x1bc2b0)
    (h0 : s.regs 0 = BitVec.ofNat 64 st) (h1 : s.regs 1 = BitVec.ofNat 64 zp)
    (h2 : s.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : s.regs 3 = BitVec.ofNat 64 zc)
    (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 n) (h6 : s.regs 6 = BitVec.ofNat 64 xc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ S1 : State, S1.pc = BitVec.ofNat 64 kL1 → S1.sp = s.sp - 320#64 →
      S1.regs 0 = BitVec.ofNat 64 st → S1.regs 1 = BitVec.ofNat 64 zp → S1.regs 2 = BitVec.ofNat 64 (2 * n) →
      S1.regs 3 = BitVec.ofNat 64 zc → S1.regs 4 = BitVec.ofNat 64 xp → S1.regs 5 = BitVec.ofNat 64 n →
      S1.regs 6 = BitVec.ofNat 64 xc → S1.regs 7 = BitVec.ofNat 64 (n + 1) →
      S1.regs 8 = BitVec.ofNat 64 (kn2 n) → S1.regs 9 = BitVec.ofNat 64 (kn2 n) → S1.regs 28 = s.regs 28 →
      S1.regs 29 = s.sp - 328#64 → S1.regs 18 = s.regs 18 → KQ R b L W st zp zc xp n xc s S1.mem →
      ReachesRet (LibSqr.program.link impl) ret S1 Q) :
    ReachesRet (LibSqr.program.link impl) ret s Q := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, hW, -, hglb, -, h80, hxc, hxc40, hn12, -,
    -, hxp48, -, -, hzc, hzc40, -⟩ := hpre'
  obtain ⟨-, -, h80v, -, -, -, e80, hgacc, -, hgw, -⟩ := hglb
  have eg : RunIface.gA = 7147136 := rfl
  rw [eg] at e80 hgacc hgw
  rw [e80] at h80v
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  unfold ksqrW at hW
  have hthA : s.mem.accessible 7147160 8 false = true := Memory.accessible_mono _ hgacc (by omega) (by omega)
  have hsacc : s.mem.accessible (s.sp.toNat - 328) 376 true = true :=
    Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : s.mem.accessible (s.sp.toNat - 328) 376 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear hw hLs
  have hsh : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsh2 : (BitVec.ofNat 64 (n + 1)).rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 =
      BitVec.ofNat 64 (kn2 n) := by
    rw [klsr1]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega
  have hshl : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have t80 := toInt_small (BitVec.ofNat 64 80) (by decide)
  have tn := toInt_small (BitVec.ofNat 64 n) (by simp only [BitVec.toNat_ofNat]; omega)
  janus_run [h80v, hsh, hsh2, hshl, t80, tn] until [kL1]
  refine hK _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨hpre, ?fr, ?reg, ?_, ?_, ?_⟩
  case fr => janus_frame
  case reg => simp only [Memory.regions_writeLE]
  all_goals janus_simp
  all_goals exact Nat.mod_eq_of_lt (by omega)

theorem bv_sub_ofNat {a c : Nat} (h1 : c ≤ a) (h2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- `kn2 n ≤ c` (`c < 2^40`) makes the `ASR #63` mask of `-(c - kn2 n)` all ones -/
theorem kmask (n c : Nat) (h1 : kn2 n < c) (h2 : c < 2 ^ 40) :
    (BitVec.ofNat 64 (kn2 n) &&& (0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 (kn2 n))).sshiftRight 63) =
      BitVec.ofNat 64 (kn2 n) := by
  rw [BitVec.and_comm]
  have hd : (BitVec.ofNat 64 c - BitVec.ofNat 64 (kn2 n)).toNat = c - kn2 n := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  exact neg_sshr63_and _ _ (by rw [hd]; omega) (by rw [hd]; omega)

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

/-- `AND $-2` -/
theorem kand2 (x : BitVec 64) : x &&& 18446744073709551614#64 = (x >>> 1) <<< 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551614#64)[i] = decide (0 < i) := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, c1 i hi]
  by_cases h : i = 0
  · subst h; simp
  · simp [show 1 + (i - 1) = i by omega, show ¬ i < 1 by omega, BitVec.getLsbD_eq_getElem hi] <;>
      (try (intro _; omega))

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
