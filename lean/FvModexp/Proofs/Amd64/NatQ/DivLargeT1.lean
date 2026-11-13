import FvModexp.Proofs.Amd64.NatQ.DivLargeTN
import FvModexp.Proofs.Amd64.NatQ.DivLargeShA

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeT1.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): the tail, part 1 (natdiv.go:632-636): `q = q.norm()`, `if shift != 0 { rshVU(u, u, shift) }`,
`joinD` → `rJoin` (`AtR`)

`+0x676`: `AX = [SP' + 0xf0] = q.ptr`, `CX = [SP' + 0xf8] = len q` → `q.norm()` (`qnorm`); exit `+0x69a`: `BX = cap q`,
`CMPQ CX, BX; JA panic`, `q` stored (`RSP - 64 … - 48`), `AX = shift` (`RSP - 176`), `TESTQ AX; JE rJoin`; else ABI0
args `z = x = (P, il + 1, C)` (`SP' + 0 … + 0x28`), `s = shift` (`SP' + 0x30`), `CALL rshVU.abi0` (`+0x704`, return
`+0x709`), `XORPS X15; MOVQ FS:-8, R14` → `rJoin` (`+0x716`). `atR0` / `atR1`: `AtR` from the facts (pure). Port of
`Arm64/Nat/DivLargeT1.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

theorem natLive_acc {m m' : Memory} {R : RtInv} {L : List (Nat × Nat)} {p c : Nat} (h : NatLive m R L p c)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : NatLive m' R L p c := fun h0 => by
  obtain ⟨a, b, d, e⟩ := h h0; exact ⟨a, b, by rw [hacc]; exact d, e⟩

theorem natNorm_frame {m m' : Memory} {p n : Nat} (h : NatNorm m p n)
    (hr : m'.readLE (p + 8 * (n - 1)) 8 = m.readLE (p + 8 * (n - 1)) 8) : NatNorm m' p n :=
  h.imp id (fun h => by rw [hr]; exact h)

/-- `rshVU`'s post with the argument words read (adapted from `lshQ`, DivLargeShA) -/
theorem rshQ {C : State} {m : Memory} {z n x r : Nat}
    (hz : C.mem.readLE ((C.regs 4).toNat + 8) 8 = z)
    (hn : C.mem.readLE ((C.regs 4).toNat + 16) 8 = n) (hx : C.mem.readLE ((C.regs 4).toNat + 32) 8 = x)
    (hs : C.mem.readLE ((C.regs 4).toNat + 56) 8 = r) (h : RshVUSum.Q C m) :
    natVal m z n = natVal C.mem x n / 2 ^ r ∧
      MemFrame C.mem m [(z, z + 8 * n), ((C.regs 4).toNat + 64, (C.regs 4).toNat + 72)] := by
  unfold RshVUSum.Q at h
  rw [hz, hn, hx, hs] at h
  exact ⟨h.1, h.2.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `AtR` from `AtD` after writes `ws` inside the window below `RSP - 40` (outside `u`'s words) and `u` overwritten
with `uv` (pure; both tail paths) -/
theorem atR_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtD R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S)
    {ql : Nat} (hql : ql ≤ il - vl + 1) (hqv : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl)
    (hqn : NatNorm S.mem qp ql) (T : State) (hpc : T.rip = BitVec.ofNat 64 rJoin)
    (hsp : T.regs 4 = s.regs 4 - 304#64) (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14)
    (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0#128) (hdf : T.df = false)
    (ws : List (Nat × Nat)) (hws : ∀ r ∈ ws, (s.regs 4).toNat - 312 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40 ∧
      (r.2 ≤ (s.regs 4).toNat - 209 ∨ (s.regs 4).toNat - 88 ≤ r.1))
    (hF : MemFrame S.mem T.mem (ws ++ [(P, P + 8 * (il + 1))]))
    (hrv : natVal T.mem P (il + 1) = natVal s.mem ip il % natVal s.mem vp vl)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 T.mem))
    (hq0 : T.mem.readLE ((s.regs 4).toNat - 64) 8 = qp) (hq1 : T.mem.readLE ((s.regs 4).toNat - 56) 8 = ql)
    (hq2 : T.mem.readLE ((s.regs 4).toNat - 48) 8 = qc) (hreg : T.mem.regions = S.mem.regions) :
    AtR R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hS.ua
  have hQ := hS.qa
  have hcap := hU.cap; have hqcap := hQ.cap
  have hpw := hU.pw
  have hpu := hQ.pu; unfold Apart at hpu
  have hacc : ∀ a n w, T.mem.accessible a n w = S.mem.accessible a n w := fun a n w => hF.accessible a n w
  have hwo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 312 ∨ (s.regs 4).toNat - 40 ≤ a) → Outside a n ws := fun a n h =>
    outside_of_forall fun r hr => by have := hws r hr; omega
  have rq : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) → (a + n ≤ P ∨ P + 8 * C ≤ a) →
      T.mem.readLE a n = S.mem.readLE a n := fun a n h1 h2 =>
    hF.readLE a n (by rw [outside_append]; exact ⟨hwo a n (by omega), by
      simp only [outside_cons, outside_nil, and_true]; omega⟩)
  have hLs : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ r.1 :=
    fun r hr => hl.lsep r (hE.ext.mem_old hr)
  refine ⟨hpc, hsp, h5, h14, hfs, hx15, hdf,
    MemU.frame hE hS.mem (hU.live hS.ext4) (hF.mono fun a n ho => ?_) ⟨fun a n hin ho => ?_⟩ hinv,
    hq0, hq1, hq2, hU.frame hacc, hQ.frame hacc, hS.ext3, hS.ext4, hS.bud, hS.arr2, natLive_acc hS.live2 hacc,
    hS.c2len, hS.c2b, hql, ?_, ?_, hrv, by rw [hreg]; exact hS.reg, hS.arrL2, hS.qL⟩
  · simp only [outside_append] at ho
    obtain ⟨⟨⟨-, h2⟩, -⟩, h4⟩ := ho
    have h2' := h2
    simp only [scrB, outside_cons, outside_nil, and_true] at h2'
    simp only [outside_cons, outside_nil, and_true] at h4
    rw [outside_append]
    refine ⟨outside_of_forall fun r hr => ?_, by simp only [outside_cons, outside_nil, and_true]; omega⟩
    have := hws r hr; omega
  · rw [outside_append] at ho
    have h4 := ho.2
    simp only [outside_cons, outside_nil, and_true] at h4
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    exact hF.readLE a n (by
      rw [outside_append]; exact ⟨hwo a n (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩)
  · rw [← hqv]; unfold natVal; exact rq _ _ (by have := hQ.pw; omega) (by omega)
  · exact natNorm_frame hqn (rq _ _ (by have := hQ.pw; omega) (by omega))

/-- the `Outside` facts of the `rshVU` path (pure; stated before the run so its context stays small) -/
theorem t1_outs {sp fs P C il : Nat} (h0 : 41272 ≤ sp) (h1 : sp + 112 ≤ 2 ^ 48)
    (hpw : P + 8 * C ≤ sp - 41272 ∨ sp + 112 ≤ P) (hcap : il + 1 ≤ C)
    (htw : Apart (fs - 8) 8 (sp - 41272) (41272 + 112)) (hpt : Apart P (8 * C) (fs - 8) 8) :
    Outside (fs - 8) 8 ([(sp - 312, sp - 248), (sp - 64, sp - 40)] ++ [(P, P + 8 * (il + 1)),
        (sp - 312 + 64, sp - 312 + 72)]) ∧
      (∀ a n, Outside a n ([(sp - 312, sp - 240), (sp - 64, sp - 40)] ++ [(P, P + 8 * (il + 1))]) →
        Outside a n ([(sp - 312, sp - 248), (sp - 64, sp - 40)] ++ [(P, P + 8 * (il + 1)),
          (sp - 312 + 64, sp - 312 + 72)])) ∧
      (∀ a, sp - 64 ≤ a → a + 8 ≤ sp - 40 → Outside a 8 [(P, P + 8 * (il + 1)), (sp - 312 + 64, sp - 312 + 72)]) := by
  unfold Apart at htw hpt
  refine ⟨?_, fun a n ho => ?_, fun a h1 h2 => ?_⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true]; omega
  · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  · simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- after `rshVU` returns (`+0x709`): `XORPS X15; MOVQ FS:-8, R14` → `rJoin`, `AtR` -/
theorem t1r (impl : List Amd64.Segment)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtD R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S)
    {ql : Nat} (hql : ql ≤ il - vl + 1) (hqv : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl)
    (hqn : NatNorm S.mem qp ql) (T : State) (hpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x709))
    (hsp : T.regs 4 = s.regs 4 - 304#64) (h5 : T.regs 5 = s.regs 4 - 8#64) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false)
    (hF : MemFrame S.mem T.mem ([((s.regs 4).toNat - 312, (s.regs 4).toNat - 240),
      ((s.regs 4).toNat - 64, (s.regs 4).toNat - 40)] ++ [(P, P + 8 * (il + 1))]))
    (htls : T.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat)
    (htacc : T.mem.accessible (s.fsBase.toNat - 8) 8 false = true)
    (hrv : natVal T.mem P (il + 1) = natVal s.mem ip il % natVal s.mem vp vl)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 T.mem))
    (hq0 : T.mem.readLE ((s.regs 4).toNat - 64) 8 = qp) (hq1 : T.mem.readLE ((s.regs 4).toNat - 56) 8 = ql)
    (hq2 : T.mem.readLE ((s.regs 4).toNat - 48) 8 = qc) (hreg : T.mem.regions = S.mem.regions) (Q : State → Prop)
    (k : ∀ T, AtR R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0
  have h14v : BitVec.ofNat 64 (s.regs 14).toNat = s.regs 14 := BitVec.ofNat_toNat _ _
  obtain ⟨⟨htb, -, -⟩, -, -⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
  janus64_run [htls, hfs] until [rJoin]
  refine k _ (atR_of hE hS hql hqv hqn _ rfl ?_ ?_ ?_ ?_ rfl ?_ _ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) hF hrv hinv hq0 hq1 hq2 hreg)
  all_goals (try janus64_simp)
  all_goals first | exact hsp | exact h5 | exact hfs | exact hdf | (simp only [BitVec.setWidth_eq, h14v]) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
/-- from `q.norm()`'s exit (`RCX = ql`): `q` stored, the `shift` test, then `rJoin` directly or over `rshVU` -/
theorem t1c (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtD R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S)
    {ql : Nat} (hql : ql ≤ il - vl + 1) (hqv : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl)
    (hqn : NatNorm S.mem qp ql) (X : State) (hpc : X.rip = BitVec.ofNat 64 qExit) (hm : X.mem = S.mem)
    (h0 : X.regs 0 = BitVec.ofNat 64 qp) (h1 : X.regs 1 = BitVec.ofNat 64 ql) (hsp : X.regs 4 = s.regs 4 - 304#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hx15 : X.xmm 15 = 0#128) (hdf : X.df = false) (Q : State → Prop)
    (k : ∀ T, AtR R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) X Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hMU := hS.mem
  have hM := hMU.mem
  have hU := hS.ua; have hQ := hS.qa
  have hcap := hU.cap; have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48; have hc40 := hU.c40
  have hp48 := hU.p48; have hpw := hU.pw
  have m1 : X.mem.readLE ((s.regs 4).toNat - 48) 8 = qc := by rw [hm]; exact hS.sq2
  have m2 : X.mem.readLE ((s.regs 4).toNat - 176) 8 = sh := by rw [hm]; exact hMU.ssh
  have m3 : X.mem.readLE ((s.regs 4).toNat - 104) 8 = P := by rw [hm]; exact hMU.sP
  have m4 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = il + 1 := by rw [hm]; exact hMU.sL
  have m5 : X.mem.readLE ((s.regs 4).toNat - 184) 8 = C := by rw [hm]; exact hMU.sC
  have hsh63 := hS.sh63
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hE.pre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg hal
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hm, hM.fr.accessible]
  have hwacc : X.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hXacc]; exact hw
  have hwaccS : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    rw [hM.fr.accessible]; exact hw
  have n1 := hS.sq2; have n2 := hMU.ssh; have n3 := hMU.sP; have n4 := hMU.sL; have n5 := hMU.sC
  have hreg : X.mem.regions = s.mem.regions := by rw [hm]; exact hS.reg
  have hqv' : natVal X.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl := by rw [hm]; exact hqv
  have hqn' : NatNorm X.mem qp ql := by rw [hm]; exact hqn
  -- the `AtR` facts at `X` (memory = `S`'s)
  by_cases hsh : sh = 0
  · have m2' : X.mem.readLE ((s.regs 4).toNat - 176) 8 = 0 := by rw [m2, hsh]
    have n2' : S.mem.readLE ((s.regs 4).toNat - 176) 8 = 0 := by rw [n2, hsh]
    janus64_run [m1, m2', n1, n2'] until [rJoin]
    refine k _ (atR_of hE hS hql hqv hqn _ rfl ?_ ?_ ?_ ?_ ?_ ?_ [((s.regs 4).toNat - 64, (s.regs 4).toNat - 40)]
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp only; omega)
      (by simp only [List.cons_append, List.nil_append]; janus_frame) ?_ ?_ ?_ ?_ ?_
      (by simp only [Janus.Arm64.Memory.regions_writeLE]))
    case refine_7 =>
      have := hS.rval; rw [hsh, Nat.pow_zero, Nat.mul_one] at this
      rw [← this]; unfold natVal
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    case refine_8 =>
      refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 64, (s.regs 4).toNat - 40)]) (by janus_frame)
        (fun r hr => ?_) hMU.mem.inv
      simp only [List.mem_singleton] at hr; subst hr
      left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    all_goals (try janus64_simp)
    all_goals first
      | exact h5 | exact h14 | exact hfs | exact hx15 | exact hdf | rfl
      | (simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Nat.reducePow]; omega)
      | skip
  · have hne : (BitVec.ofNat 64 sh = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have hgacc : X.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hXacc]; exact hg2
    have htacc : X.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hXacc]; exact htr
    have htS : X.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by rw [hm]; exact hM.tls
    have hgrd : X.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      rw [hm]; exact hMU.grd
    -- `rshVU`'s precondition facts (callee `RSP = RSP - 312`; `z = x = P`, `n = il + 1`)
    have hzH : Held R L2 P (8 * (il + 1)) := (hS.ext4.held hU.pheld).sub (by omega) (by omega)
    have hzacc : S.mem.accessible P (8 * (il + 1)) true = true :=
      Janus.Arm64.Memory.accessible_mono _ hU.pacc (by omega) (by omega)
    have hxacc : S.mem.accessible P (8 * (il + 1)) false = true :=
      Janus.Arm64.Memory.accessible_read_of_write _ hzacc
    have hro : Outside ((s.regs 4).toNat - 312 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
    have hga := hE.pre.ce.2.2.2.2.2.1
    unfold Apart at hga
    have hzg : Apart P (8 * (il + 1)) ((s.regs 14).toNat + 16) 8 := by
      have h := hU.pg; unfold Apart at h ⊢; omega
    have hzt : Apart P (8 * (il + 1)) (s.fsBase.toNat - 8) 8 := by
      have h := hU.pt; unfold Apart at h ⊢; omega
    have hrg : Apart ((s.regs 4).toNat - 312 + 64) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
    have hrt : Apart ((s.regs 4).toNat - 312 + 64) 8 (s.fsBase.toNat - 8) 8 := by
      have h := htw; unfold Apart at h ⊢; omega
    have hzr : Apart P (8 * (il + 1)) ((s.regs 4).toNat - 312) 72 := by unfold Apart; omega
    have hxr : Apart P (8 * (il + 1)) ((s.regs 4).toNat - 312 + 64) 8 := by unfold Apart; omega
    have halx : P ≤ P ∨ Apart P (8 * (il + 1)) P (8 * (il + 1)) := Or.inl (Nat.le_refl _)
    have hra : (6221865 : Nat) < 2 ^ 47 := by decide
    have hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 S.mem) := hMU.mem.inv
    have hfsN : X.fsBase.toNat = s.fsBase.toNat := by rw [hfs]
    have hrt' : (s.regs 4).toNat - 312 + 64 + 8 ≤ X.fsBase.toNat - 8 ∨
        X.fsBase.toNat - 8 ≤ (s.regs 4).toNat - 312 + 56 := by
      rw [hfsN]; have h := hrt; unfold Apart at h; omega
    have htS' : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
    have htaccS : S.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hM.fr.accessible]; exact htr
    have hgrd' := hMU.grd
    janus64_run [m1, m2, m3, m4, m5, n1, n2, n3, n4, n5, htS, htS', hfs, hgrd, hgrd', hne, ite_self] until [segAddr Extracted.program fn + 0x709]
      calls [rshvu impl hap R b2 L2]
    rename_i w _ _ hq hinv1 hgd htl
    have e312 : (s.regs 4 - 312#64).toNat = (s.regs 4).toNat - 312 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    obtain ⟨q1, q3⟩ := rshQ (z := P) (n := il + 1) (x := P) (r := sh)
      (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
      (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
      (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
      (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)) hq
    simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312] at q1 q3 hinv1
    have hF1 := mfTrans (m₀ := S.mem) (rs := [((s.regs 4).toNat - 312, (s.regs 4).toNat - 248),
      ((s.regs 4).toNat - 64, (s.regs 4).toNat - 40)]) (by janus_frame) q3
    have hrv : natVal w P (il + 1) = natVal s.mem ip il % natVal s.mem vp vl := by
      rw [q1]
      have : natVal S.mem P (il + 1) = natVal s.mem ip il % natVal s.mem vp vl * 2 ^ sh := hS.rval
      unfold natVal at this ⊢
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    obtain ⟨oT, oF, oq⟩ := t1_outs hsp0 hsp1 hpw hcap htw hU.pt
    have htl' : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
      rw [hF1.readLE _ _ oT]; exact htS'
    have hTF : MemFrame S.mem w ([((s.regs 4).toNat - 312, (s.regs 4).toNat - 240),
        ((s.regs 4).toNat - 64, (s.regs 4).toNat - 40)] ++ [(P, P + 8 * (il + 1))]) :=
      hF1.mono oF
    refine t1r impl hE hS hql hqv hqn _ ?_ ?_ ?_ ?_ ?_ hTF htl' ?_ hrv hinv1 ?_ ?_ ?_ ?_ Q k
    case refine_6 => simp only [retState0]; rw [hTF.accessible]; exact htaccS
    case refine_7 =>
      simp only [retState0]; rw [q3.readLE _ _ (oq _ (by omega) (by omega))]
      simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Nat.reducePow]; omega
    case refine_8 =>
      simp only [retState0]; rw [q3.readLE _ _ (oq _ (by omega) (by omega))]
      simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Nat.reducePow]; omega
    case refine_9 =>
      simp only [retState0]; rw [q3.readLE _ _ (oq _ (by omega) (by omega))]
      simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Nat.reducePow]; omega
    case refine_10 =>
      rename_i hrg1
      simp only [retState0]; rw [hrg1]; (try simp only [Janus.Arm64.Memory.regions_writeLE])
    all_goals (try janus64_simp)
    all_goals first | exact h5 | exact hfs | exact hdf | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the tail, part 1**: `AtD` → `q = q.norm()` → `q` stored → `rshVU` (if `shift ≠ 0`) → `AtR` -/
theorem t1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtD R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 S) (Q : State → Prop)
    (k : ∀ ql T, AtR R b H L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hQ := hS.qa
  have hqcap := hQ.cap; have hq40 := hQ.c40; have hq48 := hQ.p48
  have m0 := hS.sq0; have m1 := hS.sq1
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hE.pre.ce
  simp only [regSP] at hb' ha hw
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    rw [hS.mem.mem.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  janus64_run [m0, m1] until [qHead]
  refine qnorm impl (retAddrOf s) S.mem qp (il - vl + 1) (natVal s.mem ip il / natVal s.mem vp vl) (s.regs 4 - 304#64)
    (s.regs 4 - 8#64) (s.regs 14) s.fsBase 0#128 Q
    (fun s' n' hpc' hm' h0' h1' hsp' h5' h14' hfs' hx' hdf' hle hv hn =>
      t1c impl hap R hE hS hle hv hn s' hpc' hm' h0' h1' hsp' h5' h14' hfs' hx' hdf' Q (k n'))
    (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hQ.pacc (Nat.le_refl _) (by omega)))
    (il - vl + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hS.qval
  all_goals (try janus64_simp)
  all_goals first | exact hsp | exact h5 | exact h14 | exact hfs | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Q.DivLarge
