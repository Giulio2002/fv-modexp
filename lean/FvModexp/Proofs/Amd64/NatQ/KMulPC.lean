import FvModexp.Proofs.Amd64.NatQ.KMulPN
import FvModexp.Proofs.Amd64.NatQ.KMulPD
import FvModexp.Proofs.Amd64.NatQ.KMulLoop

set_option autoImplicit false

/-!
# [amd64 port (divmc s52) of the Q-form Arm64/NatQ/KMulPC.lean — TIGHT COSTS] `karatsuba` (amd64): `y1` loop exit → the `stk.nat(2·n2 + 1)` entry (natmul.go:198-204)

`kmPC`: from `0x5f1f76` (`R10 = len y1`; the `y[n2:i]` bound check refuted) the `y0`/`y1`/`z0`/`z2` headers, the
`z[0:2n2]` / `z[2n2:]` bound checks (refuted), the spills (`RSP+40 := zp`, `RSP+56 := zc`, `RSP-344 := n2`,
`RSP-352 := 8·n2`, `RSP-360 := 2·n2`), the defer record and bit, then the call: the state at `(*stack).nat`'s entry
is `KPm`. `kpmOfX` (pure) builds `KPm` from one frame fact over the written ranges, so the unwritten slots cost no
memory simplification.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (bv_sub_ofNat bv_add_ofNat kmask kmask' kand2 kshr1 kshl1 kshl4 IntAt stkNatA)

/-- the ranges `kmPC` writes (relative to the entry `RSP`) -/
@[reducible] def kpcW (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 456, (s.regs 4).toNat - 448), ((s.regs 4).toNat - 369, (s.regs 4).toNat - 368),
    ((s.regs 4).toNat - 360, (s.regs 4).toNat - 336), ((s.regs 4).toNat - 232, (s.regs 4).toNat - 80),
    ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8), ((s.regs 4).toNat + 40, (s.regs 4).toNat + 48),
    ((s.regs 4).toNat + 56, (s.regs 4).toNat + 64)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `KPm` at `P` from `S` (`KQm`): `P.mem` differs from `S.mem` only in `kpcW s` -/
theorem kpmOfX {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {lx0 lx1 ly0 ly1 : Nat}
    (hl0 : lx0 ≤ kh n) (hv0 : natVal s.mem xp lx0 = natVal s.mem xp (kh n)) (hn0 : NatNorm s.mem xp lx0)
    (hl1 : lx1 ≤ n - kh n)
    (hv1 : natVal s.mem (xp + 8 * kh n) lx1 = natVal s.mem (xp + 8 * kh n) (n - kh n))
    (hn1 : NatNorm s.mem (xp + 8 * kh n) lx1)
    (hm0 : ly0 ≤ kh n) (hw0 : natVal s.mem yp ly0 = natVal s.mem yp (kh n)) (hmn0 : NatNorm s.mem yp ly0)
    (hm1 : ly1 ≤ n - kh n)
    (hw1 : natVal s.mem (yp + 8 * kh n) ly1 = natVal s.mem (yp + 8 * kh n) (n - kh n))
    (hmn1 : NatNorm s.mem (yp + 8 * kh n) ly1)
    (hx0 : IntAt S.mem ((s.regs 4).toNat - 48) 0 xp lx0 xc)
    (hx1 : IntAt S.mem ((s.regs 4).toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n))
    (m32 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = st) (m48 : S.mem.readLE ((s.regs 4).toNat + 48) 8 = 2 * n)
    (P : State) (hF : MemFrame S.mem P.mem (kpcW s)) (hreg : P.mem.regions = S.mem.regions)
    (hpc : P.rip = BitVec.ofNat 64 stkNatA) (hsp : (P.regs 4).toNat = (s.regs 4).toNat - 456)
    (hg : P.regs 14 = s.regs 14) (hfpr : P.regs 5 = s.regs 4 - 8#64) (hfs : P.fsBase = s.fsBase)
    (hdf : P.df = s.df) (hx : P.xmm 15 = s.xmm 15) (r0 : P.regs 0 = BitVec.ofNat 64 st)
    (r1 : P.regs 3 = BitVec.ofNat 64 (kT n)) (ra : P.mem.readLE ((s.regs 4).toNat - 456) 8 = 0x5f209b)
    (bit : P.mem.readLE ((s.regs 4).toNat - 369) 1 = 1) (q88 : P.mem.readLE ((s.regs 4).toNat - 360) 8 = 2 * kh n)
    (q96 : P.mem.readLE ((s.regs 4).toNat - 352) 8 = 8 * kh n) (q104 : P.mem.readLE ((s.regs 4).toNat - 344) 8 = kh n)
    (dfn : P.mem.readLE ((s.regs 4).toNat - 232) 8 = kDfn) (dst : P.mem.readLE ((s.regs 4).toNat - 224) 8 = st)
    (dln : P.mem.readLE ((s.regs 4).toNat - 216) 8 = stLen s.mem st)
    (dpt : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 232)
    (s2 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = zp) (s4 : P.mem.readLE ((s.regs 4).toNat + 56) 8 = zc)
    (y0h : IntAt P.mem ((s.regs 4).toNat - 112) 0 yp ly0 yc)
    (y1h : IntAt P.mem ((s.regs 4).toNat - 144) 0 (yp + 8 * kh n) ly1 (yc - kh n))
    (z0h : Z0H s P.mem zp zc n) (z2h : Z2H s P.mem zp zc n) :
    KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P := by
  have F := hQ.pre.F
  obtain ⟨-, ⟨hb', ha, -⟩, -⟩ := F.env
  simp only [regSP] at hb' ha
  have hW := F.hW; have hW' := kW64_ge n
  clear F
  have hk : ∀ x m, (x + m ≤ (s.regs 4).toNat - 456 ∨ (s.regs 4).toNat - 448 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 369 ∨ (s.regs 4).toNat - 368 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 360 ∨ (s.regs 4).toNat - 336 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 232 ∨ (s.regs 4).toNat - 80 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 16 ∨ (s.regs 4).toNat - 8 ≤ x) →
      (x + m ≤ (s.regs 4).toNat + 40 ∨ (s.regs 4).toNat + 48 ≤ x) →
      (x + m ≤ (s.regs 4).toNat + 56 ∨ (s.regs 4).toNat + 64 ≤ x) →
      P.mem.readLE x m = S.mem.readLE x m := fun x m h1 h2 h3 h4 h5 h6 h7 =>
    hF.readLE _ _ (by simp only [kpcW, outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩)
  refine
    { pre := hQ.pre, pc := hpc, sp := hsp, g := hg, fpr := hfpr, fs := hfs, df := hdf, x15 := hx, r0 := r0,
      r1 := r1, ra := ra, l0 := hl0, v0 := hv0, nn0 := hn0, l1 := hl1, v1 := hv1, nn1 := hn1,
      m0 := hm0, w0 := hw0, mn0 := hmn0, m1 := hm1, w1 := hw1, mn1 := hmn1, fr := ?fr, reg := hreg.trans hQ.reg,
      fp := ?fp, bit := bit, q88 := q88, q96 := q96, q104 := q104, dfn := dfn, dst := dst, dln := dln, dpt := dpt,
      s1 := ?s1, s2 := s2, s3 := ?s3, s4 := s4, s5 := ?s5,
      x0h := ?x0h, x1h := ?x1h, y0h := y0h, y1h := y1h, z0h := z0h, z2h := z2h }
  case fr =>
    exact hQ.fr.trans hF fun a k h => by
      simp only [kpcW, outside_cons, outside_nil, and_true] at h ⊢; omega
  case fp => rw [hk _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hQ.fp
  case s1 => rw [hk _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact m32
  case s3 => rw [hk _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact m48
  case s5 => rw [hk _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hQ.s5
  case x0h =>
    exact IntAt.keep hx0 fun x m h1 h2 => hk _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  case x1h =>
    exact IntAt.keep hx1 fun x m h1 h2 => hk _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kmPC (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {S : State} (hQ : KQm R b H L W st zp zc xp n xc yp yc s S.mem) {lx0 lx1 ly0 ly1 : Nat}
    (hl0 : lx0 ≤ kh n) (hv0 : natVal s.mem xp lx0 = natVal s.mem xp (kh n)) (hn0 : NatNorm s.mem xp lx0)
    (hl1 : lx1 ≤ n - kh n)
    (hv1 : natVal s.mem (xp + 8 * kh n) lx1 = natVal s.mem (xp + 8 * kh n) (n - kh n))
    (hn1 : NatNorm s.mem (xp + 8 * kh n) lx1)
    (hm0 : ly0 ≤ kh n) (hw0 : natVal s.mem yp ly0 = natVal s.mem yp (kh n)) (hmn0 : NatNorm s.mem yp ly0)
    (hm1 : ly1 ≤ n - kh n)
    (hw1 : natVal s.mem (yp + 8 * kh n) ly1 = natVal s.mem (yp + 8 * kh n) (n - kh n))
    (hmn1 : NatNorm s.mem (yp + 8 * kh n) ly1)
    (m32 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = st) (m48 : S.mem.readLE ((s.regs 4).toNat + 48) 8 = 2 * n)
    (hx0 : IntAt S.mem ((s.regs 4).toNat - 48) 0 xp lx0 xc)
    (hx1 : IntAt S.mem ((s.regs 4).toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n))
    (hpc : S.rip = BitVec.ofNat 64 kmLY1x) (hsp : S.regs 4 = s.regs 4 - 448#64)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 yp)
    (h7 : S.regs 7 = BitVec.ofNat 64 zc) (h6 : S.regs 6 = BitVec.ofNat 64 (yp + 8 * kh n))
    (h8 : S.regs 8 = BitVec.ofNat 64 yc) (h9 : S.regs 9 = BitVec.ofNat 64 (yc - kh n))
    (h10 : S.regs 10 = BitVec.ofNat 64 ly1)
    (h11 : S.regs 11 = BitVec.ofNat 64 (n + 1)) (h12 : S.regs 12 = BitVec.ofNat 64 (8 * kh n))
    (h15 : S.regs 15 = BitVec.ofNat 64 ly0) (h2 : S.regs 2 = BitVec.ofNat 64 (kh n))
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = s.df) (hx : S.xmm 15 = s.xmm 15)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ P : State, KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P →
      ReachesRet (LibMul.program.link impl) ret P Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have F := hQ.pre.F
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := F.env
  simp only [regSP] at hb' ha hw
  have hW := F.hW; have hW' := kW64_ge n
  have h40 := F.n40; have hyc := F.ycn; have hyc40 := F.yc40; have hn12 := F.n12
  have hzc := F.zc2; have hzc40 := F.zc40; have hx48 := F.x48; have hy48 := F.y48
  have hzl : zp + 8 * zc ≤ 2 ^ 48 := (F.zlive (by omega)).2.2.2
  obtain ⟨hst0, ⟨hst8, -, hstacc0, hst48, -⟩, hstw, -⟩ := F.stk
  clear F
  have hstacc : S.mem.accessible (st + 8) 8 false = true := by
    rw [hQ.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _
      (Janus.Arm64.Memory.accessible_sub _ hstacc0 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)) (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hk : kh n ≤ n ∧ n - kh n ≤ kh n ∧ 0 < kh n ∧ 2 * kh n ≤ n + 1 ∧ n ≤ 2 * kh n := by simp only [kh]; omega
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hw
  have eL : S.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 :=
    hQ.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have ekk : NatSqr.kn2 n = kh n := rfl
  have hand : BitVec.ofNat 64 (n + 1) &&& 18446744073709551614#64 = BitVec.ofNat 64 (2 * kh n) := by
    rw [kand2, kshr1 (by omega), ekk, kshl1 (by omega)]
  have hsl4 := kshl4 (a := kh n) (by omega)
  have hz2 : BitVec.ofNat 64 zc - BitVec.ofNat 64 (2 * kh n) = BitVec.ofNat 64 (zc - 2 * kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hn2 : BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 (2 * kh n) = BitVec.ofNat 64 (2 * n - 2 * kh n) :=
    bv_sub_ofNat (by omega) (by omega)
  have hm := kmask (zc - 2 * kh n) (16 * kh n) (by omega) (by omega)
  have hm' := kmask' (zc - 2 * kh n) (16 * kh n) (by omega) (by omega)
  have hza : BitVec.ofNat 64 zp + BitVec.ofNat 64 (16 * kh n) = BitVec.ofNat 64 (zp + 16 * kh n) :=
    bv_add_ofNat (by omega)
  have hdd : BitVec.ofNat 64 (kh n) + BitVec.ofNat 64 (kh n) = BitVec.ofNat 64 (2 * kh n) :=
    by rw [bv_add_ofNat (by omega)]; congr 1; omega
  have hkt : BitVec.ofNat 64 (2 * kh n) + 1#64 = BitVec.ofNat 64 (kT n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kT]; omega
  have hkt' : BitVec.ofNat 64 (2 * kh n) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (kT n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, kT]; omega
  have esp : (s.regs 4 - 448#64).toNat = (s.regs 4).toNat - 448 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [eL, m48, hand, hsl4, hz2, hn2, hm, hm', hza, hdd, hkt, hkt', esp, BitVec.msb_eq_decide] until [stkNatA]
  refine hK _ (kpmOfX hQ hl0 hv0 hn0 hl1 hv1 hn1 hm0 hw0 hmn0 hm1 hw1 hmn1 hx0 hx1 m32 m48 _ ?F ?reg ?pc ?sp ?g
    ?fpr ?fs ?df ?x15 ?r0 ?r1 ?ra ?bit ?q88 ?q96 ?q104 ?dfn ?dst ?dln ?dpt ?s2 ?s4 ?y0h ?y1h ?z0h ?z2h)
  clear hv0 hv1 hw0 hw1 hn0 hn1 hmn0 hmn1 hx0 hx1 hand hsl4 hz2 hn2 hm hm' hza hdd hkt hkt' eL hsacc hstacc hK
  case F => simp only [kpcW]; janus_frame
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case pc => rfl
  all_goals (try simp only [IntAt, Z0H, Z2H])
  all_goals janus64_simp
  all_goals first
    | exact Nat.mod_eq_of_lt (by omega)
    | exact hfs
    | exact hdf
    | exact hx
    | exact h14
    | skip
  all_goals first | omega | (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Amd64.Q.NatMul
