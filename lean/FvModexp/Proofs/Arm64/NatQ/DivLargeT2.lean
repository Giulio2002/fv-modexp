import FvModexp.Proofs.Arm64.NatQ.DivLargeTP
import FvModexp.Proofs.Arm64.NatQ.DivLargeCallees

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivLargeT2.lean, TIGHT COSTS, asm s38)
# `divLarge` (arm64): the tail, part 2 (natdiv.go:638-640): `r = u.norm()`, the deferred `stk.restore` (`CALL (R0)`,
`dsum`), the return → `RQ` (`Post`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `u.norm()`'s exit (`R4 = rl`): `r` stored, the deferred closure, the return -/
theorem t2c (impl : List Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 ql : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {T : State}
    (hT : AtR R b H L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    {rl : Nat} (hrl : rl ≤ il + 1) (hrv : natVal T.mem P rl = natVal s.mem ip il % natVal s.mem vp vl)
    (hrn : NatNorm T.mem P rl) (X : State) (hpc : X.pc = BitVec.ofNat 64 rExit) (hm : X.mem = T.mem)
    (h0 : X.regs 0 = BitVec.ofNat 64 P) (h4 : X.regs 4 = BitVec.ofNat 64 rl) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) X (RQ R b H L c zp zc st up uc ip il vp vl s) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hsw := hl.sw
  have hpre := hE.pre
  have hMU := hT.mem
  have hM := hMU.mem
  have hU := hT.ua; have hQ := hT.qa
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48; have hq40 := hQ.c40; have hq48 := hQ.p48
  have hqcap := hQ.cap; have hql := hT.qle
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, hga, hgr, -, -⟩ := hpre.ce
  unfold Apart at hga
  have hTacc : ∀ a n v, T.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : T.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hTacc]; exact hw
  have hsacc : T.mem.accessible st 24 true = true := by rw [hTacc]; exact hpre.sti.1.2.2.1
  have hgacc : T.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hTacc]; exact hg2
  have m1 := hM.lr; have m2 := hM.fp; have mdp := hM.dp; have mdf : T.mem.readLE (s.sp.toNat - 40) 8 = 1810160 := hM.dfn
  have mcap := hM.hcap; have mC := hMU.sC; have mq0 := hT.sq0; have mq1 := hT.sq1; have mq2 := hT.sq2
  have f8 : T.mem.readLE (s.sp.toNat - 40 + 8) 8 = st := by
    rw [show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact hM.dst
  have f16 : T.mem.readLE (s.sp.toNat - 40 + 16) 8 = stLen s.mem st := by
    rw [show s.sp.toNat - 40 + 16 = s.sp.toNat - 24 by omega]; exact hM.dn
  have eg := hMU.grd
  have hc2 := hT.c2len
  have hD : Summary (LibDivL.program.link impl) 1810160 Restore.Pre Restore.Post := dsum impl
  janus_run [m1, m2, mdp, mdf, mcap, mC, mq0, mq1, mq2, f8, f16, eg] calls [hD]
  rename_i h18C h28C h29C hlen hFF _
  have hFE : MemFrame T.mem ((((T.mem.writeLE (s.sp.toNat - 88) 8 P).writeLE (s.sp.toNat - 80) 8 rl).writeLE
      (s.sp.toNat - 72) 8 C).writeLE (s.sp.toNat - 201) 1 0)
      [(s.sp.toNat - 88, s.sp.toNat - 64), (s.sp.toNat - 201, s.sp.toNat - 200)] := by janus_frame
  have hW : MemFrame T.mem _ (finW s st) := (mfTrans hFE hFF).mono fun a n ho => by
    simp only [finW, outside_cons, outside_nil, and_true] at ho
    simp only [outside_append, outside_cons, outside_nil, and_true]; omega
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, lpost hE hT hrl hrv hrn hW hlen _ rfl ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at h28C ⊢; rw [h28C, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at h18C ⊢; rw [h18C, h18]
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the tail, part 2**: `AtR` → `r = u.norm()` → `r` stored → `stk.restore` → return (`RQ`) -/
theorem t2 (impl : List Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 ql : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (T : State)
    (hT : AtR R b H L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) T (RQ R b H L c zp zc st up uc ip il vp vl s) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hT.ua
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have m0 := hT.mem.sP; have m1 := hT.mem.sL
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : T.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hT.mem.mem.fr.accessible]; exact hw
  have hpc := hT.pc; have hsp := hT.sp; have h28 := hT.r28; have h29 := hT.r29; have h18 := hT.r18
  janus_run [m0, m1] until [rHead]
  refine rnorm impl (s.regs 30) T.mem P (il + 1) (natVal s.mem ip il % natVal s.mem vp vl) (s.sp - 304#64)
    (s.regs 28) (s.sp - 312#64) (s.regs 18) _
    (fun s' n' hpc' hm' h0' h4' hsp' h28' h29' h18' hle hv hn =>
      t2c impl R hE hT hl4 hl48 hle hv hn s' hpc' hm' h0' h4' hsp' h28' h29' h18')
    (by omega) (by omega)
    (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hU.pacc (Nat.le_refl _) (by omega)))
    (il + 1) _ (Nat.le_refl _) rfl ?_ ?_ rfl ?_ ?_ ?_ rfl hT.rval
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]

end FvModexp.Arm64.Q.DivLarge
