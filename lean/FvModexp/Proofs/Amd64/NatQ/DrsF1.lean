import FvModexp.Proofs.Amd64.NatQ.DrsFRel
import FvModexp.Proofs.Common.DivmcBits

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF1.lean; adapted from Amd64/NatQ/DrsB1.lean)
# `divRecursiveStep` (amd64), final block: `clear(qhat)` (natdiv.go:860-861)

`f1`: from the loop head `H` (`0x5efa5f`) with `j ≤ B` (`JLE` → `0x5f00d0`): `TESTQ BX, BX` (`B + 1 ≠ 0`),
`RBX = 8·(B+1)` → `CALL runtime.memclrNoHeapPointers` at `0x5f00e0` (`qhat0`); `f1c`: from the callee entry to its
return `0x5f00e5` (`AF1`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the own store of `f1`: the return slot of the call -/
@[reducible] def isF1 (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the final block's `clear(qhat)` call, from the callee entry `X` -/
theorem f1c (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (hH : H R c s Lk bk S j)
    (hj : j ≤ c.vl / 2) (Q : State → Prop)
    (k : ∀ S', AF1 R c s Lk bk S' j (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers"))
    (hsp : X.regs 4 = s.regs 4 - 400#64) (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h3 : X.regs 3 = BitVec.ofNat 64 (8 * (c.vl / 2 + 1)))
    (hF4 : MemFrame S.mem X.mem (isF1 s)) (hreg : X.mem.regions = S.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rF1) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hH.cr
  have hev := hH.ev
  have hpre := hcr.pre
  have hce := hpre.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hv9 := hpre.v9.1
  obtain ⟨-, -, hqh, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvw, -, -, -⟩ := hpre.va
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hx : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hF : MemFrame S.mem X.mem (fw s) := hF4.mono fun x n ho => by
    simp only [fw, win, isF1, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hev hF hreg
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := Fp.own hcr hH.fp hF
  have rd4 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF4.readLE _ _ (by simp only [win, isF1, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hsl : Sl c s X.mem := hH.sl.frame hF4 (by simp only [FixOut, isF1, outside_cons, outside_nil, and_true]; omega)
  have ht0w := hcr.t0w
  have ht48 := hcr.t048
  have e0 : (X.regs 0).toNat = c.t0 := by rw [h0, BitVec.toNat_ofNat]; omega
  have e3' : (X.regs 3).toNat = 8 * (c.vl / 2 + 1) := by rw [h3, BitVec.toNat_ofNat]; omega
  refine ReachesRet.call_regions (hmc Lk bk) hpc (mcL_pre hce (by omega) hpre.sv hx X (by omega) h14
    (hEvX.grd hcr) (fun a n w => hEvX.fr.accessible a n w) (by rw [hspn, hra]; decide) hx15 hdf hEvX.inv e0 e3'
    (by omega) (by omega) (by rw [hEvX.fr.accessible]; exact hcr.t0acc) (hev.ext.held hcr.t0h) ht0w) ?_
  intro T hT ⟨junk, f, xx, yh, m, zh, kr, hs, hMF, hLF, hinv', hzr⟩ hrg
  subst hs
  rw [e0, e3'] at hMF hLF hzr
  have hMFw : MemFrame X.mem m (R.rt ++ win X 4096 24 ++ [(c.t0, c.t0 + 8 * (c.vl / 2 + 1))]) :=
    hMF.mono fun x n ho => by
      simp only [calleeStack64, win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  have hS : ∀ x n, Outside x n (win s c.W 96) → Outside x n (win X 4096 24) := fun x n ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hst : Outside c.st 24 [(c.t0, c.t0 + 8 * (c.vl / 2 + 1))] := by
    have := hcr.t0st; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  rw [h14] at hinv'
  have hreg' : m.regions = X.mem.regions := by rw [← hrg]; rfl
  have hEvT : Ev R c s Lk bk m := Ev.callN hcr hEvX hMFw hLF hS hloc.1 hloc.2 hst hinv' hreg'
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr hEvX hMFw hLF hS hst
  have kp : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.t0 (8 * (c.vl / 2 + 1)) →
      m.readLE x n = S.mem.readLE x n := by
    intro x n hh hw' hap
    rw [Held.readLE2 hh hMFw hLF (hS _ _ hw')
      (by unfold Apart at hap; simp only [outside_cons, outside_nil, and_true]; omega)]
    exact rd4 x n hw'
  have t0q := hcr.t0q; have t0u := hcr.t0u; have t0v := hcr.t0v
  unfold Apart at t0q t0u t0v
  have kv := kp _ _ (hx.held hvh) hvw (by unfold Apart; omega)
  have ku : m.readLE c.up (8 * c.u1) = S.mem.readLE c.up (8 * c.u1) :=
    kp _ _ (hx.held (huh.sub (Nat.le_refl _) (by omega))) (huw.of_sub (by omega) (by omega)) (by unfold Apart; omega)
  have kt : m.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega)) (by unfold Apart; omega)
  have kq := kp _ _ (hx.held hqh) hqw (by unfold Apart; omega)
  have hslT : Sl c s m := by
    refine hsl.frame hMFw ?_
    refine fixOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at ht0w ⊢; omega
  have hbud : c.lo s + c.K s + stkR c.Hq m c.st ≤ bk := by
    have h1 : c.K s ≤ (j / (c.vl / 2) + 1) * c.K s := Nat.le_mul_of_pos_left (c.K s) (Nat.succ_pos _)
    have h2 := hH.bud
    rw [stkR_congr (eC.trans (Cr.capOwn hcr hF))]
    omega
  refine k _ ⟨?pc, ?sp, ?r5, ?r14, hfs, hdf, ?x15, hcr, hEvT, Fp.hdr hFpX eW eL eC, hslT,
    kv.trans hH.vk, kt.trans hH.utl,
    limbs_congr kq, hj, hH.li, limbs_congr ku, FvModexp.Expmc.readLE_zeroed hzr, hbud⟩
  case pc => rw [hT]; simp only [retAddrOf]; rw [hspn, hra]
  case sp =>
    simp only [retState64, callRegs64_apply, ite_true]
    exact sp_ret400 hspn (by omega)
  case r5 =>
    simp only [retState64, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 =>
    simp only [retState64, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case x15 => simp only [retState64, ite_true]; exact hx15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the final block, part 1**: from the loop head (`j ≤ B`) to the return of `clear(qhat)` -/
theorem f1 (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (hH : H R c s Lk bk S j)
    (hj : j ≤ c.vl / 2) (Q : State → Prop)
    (k : ∀ S', AF1 R c s Lk bk S' j (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hcr := hH.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40
  have hv9 := hpre.v9.1
  have hsl := hH.sl
  have hpc := hH.pc; have hsp := hH.sp; have h0 := hH.r0; have h3 := hH.r3; have h1 := hH.r1; have h2 := hH.r2
  have rB := hsl.bb
  have hspS : (S.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hne : (BitVec.ofNat 64 (c.vl / 2 + 1) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hb3 : BitVec.ofNat 64 (c.vl / 2 + 1) <<< 3 = BitVec.ofNat 64 (8 * (c.vl / 2 + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hH.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  rcases Nat.lt_or_ge j (c.vl / 2) with hlt | hge
  · have hsub : (BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2)).msb = true := by
      rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hnz : (BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2) = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    janus64_run [rB, hsub, hnz, hne, hb3, BitVec.msb_eq_decide] until [cA "runtime.memclrNoHeapPointers"]
    refine f1c impl R hmc c s Lk bk S j hH hj Q k _ rfl ?sp ?r5 ?r14 hH.fs hH.df hH.x15 ?r0 ?r3 ?fr ?reg ?ra
    case fr => unfold isF1; janus_frame
    case reg => janus64_simp
    case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hH.r5
    case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hH.r14
    case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h0
    case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    case ra => rw [Janus.Arm64.Memory.readLE_writeLE_self]
  · have hjB : j = c.vl / 2 := by omega
    have hz : BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2) = 0#64 := by rw [hjB]; exact BitVec.sub_self _
    janus64_run [rB, hz, hne, hb3, BitVec.msb_eq_decide] until [cA "runtime.memclrNoHeapPointers"]
    refine f1c impl R hmc c s Lk bk S j hH hj Q k _ rfl ?sp ?r5 ?r14 hH.fs hH.df hH.x15 ?r0 ?r3 ?fr ?reg ?ra
    case fr => unfold isF1; janus_frame
    case reg => janus64_simp
    case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hH.r5
    case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hH.r14
    case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h0
    case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    case ra => rw [Janus.Arm64.Memory.readLE_writeLE_self]

end FvModexp.Amd64.Q.DivRec
