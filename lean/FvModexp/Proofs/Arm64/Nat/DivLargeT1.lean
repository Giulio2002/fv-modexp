import FvModexp.Proofs.Arm64.Nat.DivLargeTN
import FvModexp.Proofs.Arm64.Nat.DivLargeShP

set_option autoImplicit false

/-!
# `divLarge` (arm64): the tail, part 1 (natdiv.go:632-636): `q = q.norm()`, `if shift != 0 { rshVU(u, u, shift) }`,
`joinD` → `rJoin` (`AtR`)

`t1r`: at `rshVU.abi0`'s entry, the call, `AtR`. `t1c`: from `q.norm()`'s exit: q stored, the `shift` test, to `rJoin`
(`shift = 0`) or to `rshVU` (`t1r`). `t1`: `AtD` → `q.norm()` (`qnorm`) → `t1c`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

theorem natLive_acc {m m' : Memory} {R : RtInv} {L : List (Nat × Nat)} {p c : Nat} (h : NatLive m R L p c)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : NatLive m' R L p c := fun h0 => by
  obtain ⟨a, b, d, e⟩ := h h0; exact ⟨a, b, by rw [hacc]; exact d, e⟩

theorem natNorm_frame {m m' : Memory} {p n : Nat} (h : NatNorm m p n)
    (hr : m'.readLE (p + 8 * (n - 1)) 8 = m.readLE (p + 8 * (n - 1)) 8) : NatNorm m' p n :=
  h.imp id (fun h => by rw [hr]; exact h)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `rshVU.abi0`'s entry (`u = u >> shift` in place): the call, then `AtR` -/
theorem t1r (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtD R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S) (hsh0 : sh ≠ 0)
    {ql : Nat} (hql : ql ≤ il - vl + 1) (hqv : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl)
    (hqn : NatNorm S.mem qp ql)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program rshVUfn)) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rJoin) (hF : MemFrame S.mem X.mem (scrB s))
    (hz : X.mem.readLE (s.sp.toNat - 296) 8 = P) (hn : X.mem.readLE (s.sp.toNat - 288) 8 = il + 1)
    (hx : X.mem.readLE (s.sp.toNat - 272) 8 = P) (hs : X.mem.readLE (s.sp.toNat - 248) 8 = sh)
    (hq0 : X.mem.readLE (s.sp.toNat - 64) 8 = qp) (hq1 : X.mem.readLE (s.sp.toNat - 56) 8 = ql)
    (hq2 : X.mem.readLE (s.sp.toNat - 48) 8 = qc) (hXreg : X.mem.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ T, AtR R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hp48 := hU.p48
  have hspn : X.sp.toNat = s.sp.toNat - 304 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hMU := hS.mem
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF.accessible, hMU.mem.fr.accessible]
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hshb : 1 ≤ sh ∧ sh ≤ 63 := ⟨Nat.pos_of_ne_zero hsh0, hS.sh63⟩
  have hinvX : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 X.mem) :=
    RtInv.inv_frame' hF (fun r hr => by
      simp only [scrB, List.mem_cons, List.not_mem_nil, or_false] at hr
      left; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hout.of_sub (by simp only; omega) (by simp only; omega)) hMU.mem.inv
  have hpre := (lsh_pre (bk := b2) (Lk := L2) hE X hspn h28 (z := P) (x := P) (n := il + 1) (sh := sh)
    (by rw [hspn, show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega]; exact hz)
    (by rw [hspn, show s.sp.toNat - 304 + 16 = s.sp.toNat - 288 by omega]; exact hn)
    (by rw [hspn, show s.sp.toNat - 304 + 32 = s.sp.toNat - 272 by omega]; exact hx)
    (by rw [hspn, show s.sp.toNat - 304 + 56 = s.sp.toNat - 248 by omega]; exact hs)
    (by rw [h30]; decide) (by rw [h30]; decide) hXacc
    (by rw [hXacc]; exact Memory.accessible_mono _ (by rw [← hMU.mem.fr.accessible]; exact hU.pacc) (by omega) (by omega))
    (by
      rw [hXacc]
      exact Memory.accessible_read_of_write _
        (Memory.accessible_mono _ (by rw [← hMU.mem.fr.accessible]; exact hU.pacc) (by omega) (by omega)))
    hshb.1 hshb.2 (Or.inl (Nat.le_refl _)) (Or.inl (Nat.le_refl _)) (by have := hU.pw; omega) (by have := hU.pw; omega)
    ((hS.ext4.held hU.pheld).sub (by omega) (by omega)) (by have := hU.pg; unfold Apart at this ⊢; omega) hinvX).2
  refine ReachesRet.call_regions (rshvu impl hap R b2 L2) hpc hpre ?_
  intro T hT ⟨junk, f, v, fpsr, m4, hs4, hq, hinv4, _⟩ hrg
  subst hs4
  unfold RshVUSum.Q at hq
  rw [hspn, show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega, show s.sp.toNat - 304 + 16 = s.sp.toNat - 288 by omega,
    show s.sp.toNat - 304 + 32 = s.sp.toNat - 272 by omega, show s.sp.toNat - 304 + 56 = s.sp.toNat - 248 by omega,
    show s.sp.toNat - 304 + 64 = s.sp.toNat - 240 by omega, show s.sp.toNat - 304 + 72 = s.sp.toNat - 232 by omega,
    hz, hn, hx, hs] at hq
  obtain ⟨q1, -, q3⟩ := hq
  rw [h28] at hinv4
  -- the frames from `S`
  have hpw := hU.pw
  have hF4 : MemFrame S.mem m4 (R.rt ++ scrB s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) :=
    (mfTrans hF q3).mono fun a n ho => by
      rw [outside_append, outside_append, outside_append] at ho
      obtain ⟨⟨⟨-, h2⟩, -⟩, h4⟩ := ho
      have h2' := h2
      simp only [scrB, outside_cons, outside_nil, and_true] at h2'
      simp only [outside_cons, outside_nil, and_true] at h4
      rw [outside_append]
      exact ⟨h2, by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, by omega⟩⟩
  have hLs : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ r.1 :=
    fun r hr => hl.lsep r (hE.ext.mem_old hr)
  have hlf : LiveFrame S.mem m4 L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := ⟨fun a n hin ho => by
    rw [outside_append] at ho
    have h4 := ho.2
    simp only [outside_cons, outside_nil, and_true] at h4
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    rw [q3.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, by omega⟩)]
    exact hF.readLE a n (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)⟩
  have hacc : ∀ a n w, m4.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [q3.accessible, hF.accessible]
  have hQ := hS.qa
  have hqcap := hQ.cap; have hqw := hQ.pw
  have hpu := hQ.pu; unfold Apart at hpu
  have rq : ∀ a n, a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a → a + n ≤ P ∨ P + 8 * C ≤ a →
      m4.readLE a n = S.mem.readLE a n := fun a n h1 h2 => by
    rw [q3.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, by omega⟩)]
    exact hF.readLE a n (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)
  have rs : ∀ a, s.sp.toNat - 88 ≤ a → a + 8 ≤ s.sp.toNat - 40 → m4.readLE a 8 = X.mem.readLE a 8 := fun a h1 h2 =>
    q3.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, by omega⟩)
  refine k _ ⟨by rw [hT, h30], by simp only [retState0]; exact hsp,
    by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h28],
    by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h29],
    by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h18],
    MemU.frame hE hMU (hU.live hS.ext4) hF4 hlf hinv4, (rs _ (by omega) (by omega)).trans hq0, (rs _ (by omega) (by omega)).trans hq1,
    (rs _ (by omega) (by omega)).trans hq2, hU.frame hacc, hQ.frame hacc, hS.ext3, hS.ext4, hS.bud, hS.arr2,
    natLive_acc hS.live2 hacc, hS.c2len, hS.c2b, hql, ?_, ?_, ?_, by simp only [retState0] at hrg ⊢; rw [hrg]; exact hXreg, hS.arrL2, hS.qL⟩
  · rw [← hqv]; unfold natVal; exact rq _ _ (by omega) (by omega)
  · exact natNorm_frame hqn (rq _ _ (by omega) (by omega))
  · have q1' : natVal m4 P (il + 1) = natVal X.mem P (il + 1) / 2 ^ sh := q1
    show natVal m4 P (il + 1) = _
    rw [q1']
    have : natVal X.mem P (il + 1) = natVal S.mem P (il + 1) := by
      unfold natVal; exact hF.readLE _ _ (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)
    rw [this, hS.rval, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `shift = 0`: `AtR` after the `q` stores (pure) -/
theorem atR0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtD R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S) (hsh : sh = 0)
    {ql : Nat} (hql : ql ≤ il - vl + 1) (hqv : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl)
    (hqn : NatNorm S.mem qp ql) (T : State) (hpc : T.pc = BitVec.ofNat 64 rJoin) (hsp : T.sp = s.sp - 304#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 312#64) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame S.mem T.mem [(s.sp.toNat - 64, s.sp.toNat - 40)])
    (hq0 : T.mem.readLE (s.sp.toNat - 64) 8 = qp) (hq1 : T.mem.readLE (s.sp.toNat - 56) 8 = ql)
    (hq2 : T.mem.readLE (s.sp.toNat - 48) 8 = qc) (hreg : T.mem.regions = S.mem.regions) :
    AtR R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hS.ua
  have hQ := hS.qa
  have hcap := hU.cap; have hqcap := hQ.cap
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hacc : ∀ a n w, T.mem.accessible a n w = S.mem.accessible a n w := fun a n w => hF.accessible a n w
  have rq : ∀ a n, a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a → T.mem.readLE a n = S.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hLs : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ r.1 :=
    fun r hr => hl.lsep r (hE.ext.mem_old hr)
  refine ⟨hpc, hsp, h28, h29, h18, MemU.frame hE hS.mem (hU.live hS.ext4) (hF.mono fun a n ho => ?_) ⟨fun a n hin _ => ?_⟩ ?_,
    hq0, hq1, hq2, hU.frame hacc, hQ.frame hacc, hS.ext3, hS.ext4, hS.bud, hS.arr2, natLive_acc hS.live2 hacc,
    hS.c2len, hS.c2b, hql, ?_, ?_, ?_, by rw [hreg]; exact hS.reg, hS.arrL2, hS.qL⟩
  · rw [outside_append, outside_append, outside_append] at ho
    have h2 := ho.1.1.2
    simp only [scrB, outside_cons, outside_nil, and_true] at h2
    simp only [outside_cons, outside_nil, and_true]; omega
  · obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    exact hF.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  · exact RtInv.inv_frame' hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      left; exact hout.of_sub (by simp only; omega) (by simp only; omega)) hS.mem.mem.inv
  · rw [← hqv]; unfold natVal; exact rq _ _ (by have := hQ.pw; omega)
  · exact natNorm_frame hqn (rq _ _ (by have := hQ.pw; omega))
  · have : natVal T.mem P (il + 1) = natVal S.mem P (il + 1) := by
      unfold natVal; exact rq _ _ (by have := hU.pw; omega)
    rw [this, hS.rval, hsh, Nat.pow_zero, Nat.mul_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `q.norm()`'s exit (`R1 = ql`): `q` stored, the `shift` test, then `rJoin` or `rshVU` (`t1r`) -/
theorem t1c (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtD R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S)
    {ql : Nat} (hql : ql ≤ il - vl + 1) (hqv : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl)
    (hqn : NatNorm S.mem qp ql) (X : State) (hpc : X.pc = BitVec.ofNat 64 qExit) (hm : X.mem = S.mem)
    (h0 : X.regs 0 = BitVec.ofNat 64 qp) (h1 : X.regs 1 = BitVec.ofNat 64 ql) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18) (Q : State → Prop)
    (k : ∀ T, AtR R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hMU := hS.mem
  have hU := hS.ua; have hQ := hS.qa
  have hcap := hU.cap; have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48; have hc40 := hU.c40
  have hp48 := hU.p48
  have m1 : X.mem.readLE (s.sp.toNat - 48) 8 = qc := by rw [hm]; exact hS.sq2
  have m2 : X.mem.readLE (s.sp.toNat - 120) 8 = sh := by rw [hm]; exact hMU.ssh
  have m3 : X.mem.readLE (s.sp.toNat - 104) 8 = P := by rw [hm]; exact hMU.sP
  have m4 : X.mem.readLE (s.sp.toNat - 192) 8 = il + 1 := by rw [hm]; exact hMU.sL
  have m5 : X.mem.readLE (s.sp.toNat - 176) 8 = C := by rw [hm]; exact hMU.sC
  have hsh63 := hS.sh63
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : X.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hm, hMU.mem.fr.accessible]; exact hw
  have hreg : X.mem.regions = s.mem.regions := by rw [hm]; exact hS.reg
  have hwaccS : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hMU.mem.fr.accessible]; exact hw
  have n1 := hS.sq2; have n2 := hMU.ssh; have n3 := hMU.sP; have n4 := hMU.sL; have n5 := hMU.sC
  by_cases hsh : sh = 0
  · have m2' : X.mem.readLE (s.sp.toNat - 120) 8 = 0 := by rw [m2, hsh]
    have n2' : S.mem.readLE (s.sp.toNat - 120) 8 = 0 := by rw [n2, hsh]
    janus_run [m1, m2', n1, n2'] until [rJoin]
    refine k _ (atR0 hE hS hsh hql hqv hqn _ rfl rfl ?_ ?_ ?_ (by rw [← hm]; janus_frame) ?_ ?_ ?_
      (by simp only [Memory.regions_writeLE]))
    case refine_1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case refine_2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
    case refine_3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
    all_goals
      simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Memory.readLE_writeLE_of_disjoint, Nat.reducePow]
      omega
  · have hne : (BitVec.ofNat 64 sh = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    janus_run [m1, m2, m3, m4, m5, n1, n2, n3, n4, n5, hne] until [segAddr Extracted.program rshVUfn]
    refine t1r impl hap R hE hS hsh hql (hqv) hqn _ rfl rfl ?g28 ?g29 ?g18 ?g30 ?hF ?hz ?hn ?hx ?hs ?q0 ?q1 ?q2 ?hreg Q k
    case hF => rw [← hm]; simp only [scrB]; janus_frame
    case hreg => simp only [Memory.regions_writeLE]; exact hS.reg
    case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
    case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
    case g30 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl
    all_goals
      simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Memory.readLE_writeLE_of_disjoint, Nat.reducePow]
      omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the tail, part 1**: `AtD` → `q = q.norm()` → `q` stored → `rshVU` (if `shift ≠ 0`) → `AtR` -/
theorem t1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtD R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S) (Q : State → Prop)
    (k : ∀ ql T, AtR R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hQ := hS.qa
  have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48
  have m0 := hS.sq0; have m1 := hS.sq1
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hS.mem.mem.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  janus_run [m0, m1] until [qHead]
  refine qnorm impl (s.regs 30) S.mem qp (il - vl + 1) (natVal s.mem ip il / natVal s.mem vp vl) (s.sp - 304#64)
    (s.regs 28) (s.sp - 312#64) (s.regs 18) Q
    (fun s' n' hpc' hm' h0' h1' hsp' h28' h29' h18' hle hv hn =>
      t1c impl hap R hE hS hle hv hn s' hpc' hm' h0' h1' hsp' h28' h29' h18' Q (k n'))
    (by omega) (by omega) (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hQ.pacc (Nat.le_refl _) (by omega)))
    (il - vl + 1) _ (Nat.le_refl _) rfl ?_ ?_ rfl ?_ ?_ ?_ rfl hS.qval
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]

end FvModexp.Arm64.DivLarge
