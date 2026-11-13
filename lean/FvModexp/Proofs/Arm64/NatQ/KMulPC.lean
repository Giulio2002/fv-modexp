import FvModexp.Proofs.Arm64.NatQ.KMulPN

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/KMulPC.lean — TIGHT COSTS, divmc s34] `karatsuba` (arm64): `y1` loop exit → the `stk.nat(2·n2 + 1)` entry (natmul.go:198-204)

`kmPC`: from `0x1bbfe0` (`R8 = len y1`; the `y[n2:i]` bound check refuted) the `y0`/`y1`/`z0`/`z2` headers, the
`z[0:2n2]` / `z[2n2:]` bound checks (refuted), the spills (`SP+8 := stk`, `SP+24 := 2n`, `SP+32 := zc`, `SP-344 := n+1`,
`SP-352 := n2`, `SP-360 := 2n2`), the defer record and bit, then the call: the state at `(*stack).nat`'s entry is `KPm`.
(Adapted from this repo's `KSqrPA.kPC`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (IntAt stkNatA)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `KPm` at `P` from `S` (`KQm`): `P.mem` differs from `S.mem` only in the 4 written ranges -/
theorem kpmOf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {lx0 lx1 ly0 ly1 : Nat}
    (hl0 : lx0 ≤ kh n) (hv0 : natVal s.mem xp lx0 = natVal s.mem xp (kh n)) (hn0 : NatNorm s.mem xp lx0)
    (hl1 : lx1 ≤ n - kh n)
    (hv1 : natVal s.mem (xp + 8 * kh n) lx1 = natVal s.mem (xp + 8 * kh n) (n - kh n))
    (hn1 : NatNorm s.mem (xp + 8 * kh n) lx1)
    (hm0 : ly0 ≤ kh n) (hw0 : natVal s.mem yp ly0 = natVal s.mem yp (kh n)) (hmn0 : NatNorm s.mem yp ly0)
    (hm1 : ly1 ≤ n - kh n)
    (hw1 : natVal s.mem (yp + 8 * kh n) ly1 = natVal s.mem (yp + 8 * kh n) (n - kh n))
    (hmn1 : NatNorm s.mem (yp + 8 * kh n) ly1)
    (hx0 : IntAt S.mem (s.sp.toNat - 48) 0 xp lx0 xc)
    (hx1 : IntAt S.mem (s.sp.toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n)) (P : State)
    (hF : MemFrame S.mem P.mem [(s.sp.toNat - 361, s.sp.toNat - 336), (s.sp.toNat - 232, s.sp.toNat - 80),
      (s.sp.toNat - 16, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 40)])
    (hreg : P.mem.regions = S.mem.regions)
    (hpc : P.pc = BitVec.ofNat 64 stkNatA) (hsp : P.sp = s.sp - 448#64) (hg : P.regs 28 = s.regs 28)
    (hfpr : P.regs 29 = s.sp - 456#64) (h18 : P.regs 18 = s.regs 18) (r0 : P.regs 0 = BitVec.ofNat 64 st)
    (r1 : P.regs 1 = BitVec.ofNat 64 (kT n)) (r30 : P.regs 30 = BitVec.ofNat 64 0x1bc09c)
    (bit : P.mem.readLE (s.sp.toNat - 361) 1 = 1) (q88 : P.mem.readLE (s.sp.toNat - 360) 8 = 2 * kh n)
    (q96 : P.mem.readLE (s.sp.toNat - 352) 8 = kh n) (q104 : P.mem.readLE (s.sp.toNat - 344) 8 = n + 1)
    (dfn : P.mem.readLE (s.sp.toNat - 232) 8 = kDfn) (dst : P.mem.readLE (s.sp.toNat - 224) 8 = st)
    (dln : P.mem.readLE (s.sp.toNat - 216) 8 = stLen s.mem st)
    (dpt : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 232)
    (s1 : P.mem.readLE (s.sp.toNat + 8) 8 = st) (s2 : P.mem.readLE (s.sp.toNat + 16) 8 = zp)
    (s3 : P.mem.readLE (s.sp.toNat + 24) 8 = 2 * n) (s4 : P.mem.readLE (s.sp.toNat + 32) 8 = zc)
    (y0h : IntAt P.mem (s.sp.toNat - 112) 0 yp ly0 yc)
    (y1h : IntAt P.mem (s.sp.toNat - 144) 0 (yp + 8 * kh n) ly1 (yc - kh n))
    (z0h : Z0H s P.mem zp zc n) (z2h : Z2H s P.mem zp zc n) :
    KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P := by
  have F := hQ.pre.F
  obtain ⟨-, ⟨-, hb', ha, -⟩, -⟩ := F.env
  have hW := F.hW; have hW' := kW_ge n
  clear F
  have hk : ∀ x m, (x + m ≤ s.sp.toNat - 361 ∨ s.sp.toNat - 336 ≤ x) → (x + m ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 80 ≤ x) →
      (x + m ≤ s.sp.toNat - 16 ∨ s.sp.toNat - 8 ≤ x) → (x + m ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 40 ≤ x) →
      P.mem.readLE x m = S.mem.readLE x m := fun x m h1 h2 h3 h4 =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3, h4⟩)
  refine
    { pre := hQ.pre, pc := hpc, sp := hsp, g := hg, fpr := hfpr, r18 := h18, r0 := r0, r1 := r1, r30 := r30,
      l0 := hl0, v0 := hv0, nn0 := hn0, l1 := hl1, v1 := hv1, nn1 := hn1,
      m0 := hm0, w0 := hw0, mn0 := hmn0, m1 := hm1, w1 := hw1, mn1 := hmn1, fr := ?fr, reg := hreg.trans hQ.reg,
      lr := ?lr, fp := ?fp, bit := bit, q88 := q88, q96 := q96, q104 := q104, dfn := dfn, dst := dst,
      dln := dln, dpt := dpt, s1 := s1, s2 := s2, s3 := s3, s4 := s4, s5 := ?s5, s6 := ?s6,
      x0h := ?x0h, x1h := ?x1h, y0h := y0h, y1h := y1h, z0h := z0h, z2h := z2h }
  case fr =>
    exact hQ.fr.trans (hF.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega) fun a k h => ⟨h, h⟩
  case lr => rw [hk _ _ (by omega) (by omega) (by omega) (by omega)]; exact hQ.lr
  case fp => rw [hk _ _ (by omega) (by omega) (by omega) (by omega)]; exact hQ.fp
  case s5 => rw [hk _ _ (by omega) (by omega) (by omega) (by omega)]; exact hQ.s5
  case s6 => rw [hk _ _ (by omega) (by omega) (by omega) (by omega)]; exact hQ.s6
  case x0h => exact IntAt.keep hx0 fun x m h1 h2 => hk _ _ (by omega) (by omega) (by omega) (by omega)
  case x1h => exact IntAt.keep hx1 fun x m h1 h2 => hk _ _ (by omega) (by omega) (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPC (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {lx0 lx1 ly0 ly1 : Nat}
    (hl0 : lx0 ≤ kh n) (hv0 : natVal s.mem xp lx0 = natVal s.mem xp (kh n)) (hn0 : NatNorm s.mem xp lx0)
    (hl1 : lx1 ≤ n - kh n)
    (hv1 : natVal s.mem (xp + 8 * kh n) lx1 = natVal s.mem (xp + 8 * kh n) (n - kh n))
    (hn1 : NatNorm s.mem (xp + 8 * kh n) lx1)
    (hm0 : ly0 ≤ kh n) (hw0 : natVal s.mem yp ly0 = natVal s.mem yp (kh n)) (hmn0 : NatNorm s.mem yp ly0)
    (hm1 : ly1 ≤ n - kh n)
    (hw1 : natVal s.mem (yp + 8 * kh n) ly1 = natVal s.mem (yp + 8 * kh n) (n - kh n))
    (hmn1 : NatNorm s.mem (yp + 8 * kh n) ly1)
    (hx0 : IntAt S.mem (s.sp.toNat - 48) 0 xp lx0 xc)
    (hx1 : IntAt S.mem (s.sp.toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n))
    (hpc : S.pc = BitVec.ofNat 64 0x1bbfe0) (hsp : S.sp = s.sp - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 zp)
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : S.regs 3 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 (kh n)) (h5 : S.regs 5 = BitVec.ofNat 64 (yc - kh n))
    (h6 : S.regs 6 = BitVec.ofNat 64 (yp + 8 * kh n)) (h7 : S.regs 7 = BitVec.ofNat 64 yp)
    (h8 : S.regs 8 = BitVec.ofNat 64 ly1) (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (h10 : S.regs 10 = BitVec.ofNat 64 (n + 1)) (h12 : S.regs 12 = BitVec.ofNat 64 ly0)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 456#64) (h18 : S.regs 18 = s.regs 18)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ P : State, KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P →
      ReachesRet (LibMul.program.link impl) ret P Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -⟩ := F.env
  have hW := F.hW; have hW' := kW_ge n
  have h40 := F.n40; have hyc := F.ycn; have hyc40 := F.yc40; have hn12 := F.n12
  have hzc := F.zc2; have hzc40 := F.zc40; have hx48 := F.x48; have hy48 := F.y48
  have hzl : zp + 8 * zc ≤ 2 ^ 48 := (F.zlive (by omega)).2.2.2
  obtain ⟨hst0, ⟨hst8, -, -, hst48, -⟩, hstw, -⟩ := F.stk
  have hstacc : S.mem.accessible st 24 false = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_sub _ F.stk.2.1.2.2.1 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear F
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hk := kh_facts h40
  have hsacc : S.mem.accessible (s.sp.toNat - 456) 528 true = true := by
    rw [hQ.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hsacc' : S.mem.accessible (s.sp.toNat - 456) 528 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear hw
  have eL : S.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 :=
    hQ.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hsl1 : BitVec.ofNat 64 (kh n) <<< 1 = BitVec.ofNat 64 (2 * kh n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hand : BitVec.ofNat 64 (n + 1) &&& 18446744073709551614#64 = BitVec.ofNat 64 (2 * kh n) := by
    rw [km_and2, kh_lsr n (by omega), hsl1]
  have hsl4 : BitVec.ofNat 64 (kh n) <<< 4 = BitVec.ofNat 64 (16 * kh n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hz2 : BitVec.ofNat 64 zc - BitVec.ofNat 64 (2 * kh n) = BitVec.ofNat 64 (zc - 2 * kh n) :=
    km_sub (by omega) (by omega)
  have hn2 : BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 (2 * kh n) = BitVec.ofNat 64 (2 * n - 2 * kh n) :=
    km_sub (by omega) (by omega)
  have hm : (BitVec.ofNat 64 (kh n) &&& (0#64 - BitVec.ofNat 64 (zc - 2 * kh n)).sshiftRight 63) =
      BitVec.ofNat 64 (kh n) := by
    rw [BitVec.and_comm]
    exact neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hkt : BitVec.ofNat 64 (2 * kh n) + 1#64 = BitVec.ofNat 64 (kT n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kT]; omega
  janus_run [eL, hand, hsl1, hsl4, hz2, hn2, hm, hkt] until [stkNatA]
  refine hK _ (kpmOf hQ hl0 hv0 hn0 hl1 hv1 hn1 hm0 hw0 hmn0 hm1 hw1 hmn1 hx0 hx1 _ ?F ?reg ?pc ?sp ?g ?fpr ?r18 ?r0
    ?r1 ?r30 ?bit ?q88 ?q96 ?q104 ?dfn ?dst ?dln ?dpt ?s1 ?s2 ?s3 ?s4 ?y0h ?y1h ?z0h ?z2h)
  clear hv0 hv1 hw0 hw1 hn0 hn1 hmn0 hmn1 hx0 hx1 hsl1 hand hsl4 hz2 hn2 hm hkt eL hsacc hsacc' hstacc hK
  case F => janus_frame
  case reg => simp only [Memory.regions_writeLE]
  case pc => rfl
  all_goals (try simp only [IntAt, Z0H, Z2H])
  all_goals janus_simp
  all_goals first | exact Nat.mod_eq_of_lt (by omega) | skip
  all_goals (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.Q.NatMul
