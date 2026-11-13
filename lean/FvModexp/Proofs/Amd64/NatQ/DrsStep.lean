import FvModexp.Proofs.Amd64.NatQ.DrsLoop
import FvModexp.Proofs.Amd64.NatQ.DrsFL
import FvModexp.Proofs.Amd64.NatQ.DrsEntry
import FvModexp.Proofs.Amd64.NatQ.DrsPathA
import FvModexp.Proofs.Amd64.NatQ.DrsPathBR
import FvModexp.Proofs.Amd64.NatQ.DrsPathC
import FvModexp.Proofs.Amd64.NatQ.DrsPro2d
import FvModexp.Proofs.Amd64.NatQ.DrsSN

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsStep.lean)
# `divRecursiveStep` (amd64): the whole function (natdiv.go:750-892) by induction on `len v`

* `pro2dE`: `pro2d` (the `n < divRecursiveThreshold` test and the prologue stores) with its memory facts derived from
  `DrsPreW` and the frame `Fr` of `AtE2`.
* `drs_step`: one member case of `Summary.induction_mutual` (measure `μ = len v`): `entry` (`u.norm()`, `v.norm()`),
  then `len u = 0` (`pathA`: `clear(z)`), `n < 40` (`pathB`: `divBasic`), `len u < n` (`pathC`), and the big path
  `pro2dE` → `snH` (`stk.nat(B + 1)`) → `loop` (the wide-digit loop, recursive calls via the induction hypothesis) →
  `final` (the final block, the deferred `stk.restore`, the return).
* `sum`: the summary for every argument record (`Summary.induction_mutual`).
* **`hyp`**: `Q.DivLarge.DrsHypQ impl R drsCQ` — the premise of `divLarge` / `nat.div` — modulo the `nat.mul` premise
  (`MulHypQE` on any program `ns` without `divRecursiveStep` inside `LibDrs`) and the live runtime contracts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW DrsHypQ)

set_option maxRecDepth 20000 in
/-- `pro2d` from `AtE2`, its memory side conditions discharged from `DrsPreW` -/
theorem pro2dE (impl : List Amd64.Segment) (R : RtInv) (a : Args) (s P : State) {c : Nat}
    (hpre : DrsPreW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp a.vl a.vc s) (hW : 400 ≤ a.W) (ul' : Nat)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp a.vl a.vc a.d.toNat)
    (hle : ul' ≤ a.ul.toNat) (h0 : 0 < ul') (h40 : 40 ≤ a.vl) (hvu : a.vl ≤ ul') (Q : State → Prop)
    (k : ∀ P', AtN0 s P' a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp a.vl a.vc
      a.d.toNat → ReachesRet (LibDrs.program.link impl) (retAddrOf s) P' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P Q := by
  have hgl := hpre.gl
  have hulc := hpre.ulc
  have huc := hpre.uc40
  have hv9 := hpre.v9.1
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, -, hth, -, -, -, hgacc, -, hgw, -⟩ := hgl
  have eg : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» = 0xb4ae88 := rfl
  simp only [RunIface.gA, eg, win, outside_cons, outside_nil, and_true] at hgw hgacc hth
  have hsti := hpre.sti
  have hsacc := hsti.1.2.2.1
  have hst48 := hsti.1.2.2.2.1
  have hst := hsti.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hst
  have hF := hA.fr
  have rP : ∀ x n, Outside x n (fw s) → P.mem.readLE x n = s.mem.readLE x n := fun x n h => hF.fr.readLE x n h
  refine pro2d impl (retAddrOf s) hA h0 h40 (by omega) a.qp.isLt a.ql.isLt a.qc.isLt hst48 a.up.isLt (by omega)
    a.uc.isLt (by omega) a.d.isLt (by omega) (by omega) ?acc ?sta ?stl (by omega) ?th ?tha Q k
  case acc => rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  case sta =>
    rw [hF.fr.accessible]
    exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hsacc (by omega) (by omega))
  case stl => rw [rP _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)]
  case th => rw [rP _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)]; exact hth
  case tha => rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)

/-- **one member case** of the induction on `len v` -/
theorem drs_step (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (ns : List String) (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (n : Nat) (ih : ∀ a, IH impl R n a) (a : Args) :
    Summary (P impl) 0x5ef880 (fun s => preOf R a s ∧ μ a s = n) (postOf R a) := by
  intro s hpc ⟨⟨hE, hW, hpre⟩, hμ⟩
  have hn : a.vl = n := hμ
  subst hn
  have hWg := drsW64_ge a.vl
  refine entry impl R a s hpc hE hpre (by omega) _ fun P ul' hA hle hU hN => ?_
  rcases Nat.eq_zero_or_pos ul' with h0 | h0
  · subst h0; exact pathA impl R hmc' a s hE hpre (by omega) P hA hU
  by_cases h40 : a.vl < 40
  · exact pathB impl hap R hgr hmc hwb a s hE hpre (by omega) P ul' hA hle hU hN h0 h40
  have h40' : 40 ≤ a.vl := by omega
  by_cases hlt : ul' < a.vl
  · exact pathC impl R a s hE hpre (by omega) P ul' hA hU h0 h40' hlt
  refine pro2dE impl R a s P hpre (by omega) ul' hA hle h0 h40' (by omega) _ fun P' hN0 => ?_
  refine snH impl hap R hgr hmc hwb a s hE hpre hW P' ul' hN0 hle hU hN h40' (by omega) _ fun t0 L1 Lk bk S hH => ?_
  exact loop impl hap R ns hns hcode hmul hgr hmc hwb hmc' hmv (cOf a ul' t0 L1) ih s _
    (fun L' b' S' j' hj hH' =>
      final impl hap R ns hns hcode hmul hgr hmc hwb hmc' hmv (cOf a ul' t0 L1) ih s L' b' S' j' hj hH')
    _ _ Lk bk S (Nat.le_refl _) hH

/-- **`divRecursiveStep`'s summary** for every argument record (on `LibDrs`) -/
theorem sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (ns : List String) (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ∀ a, Summary (P impl) 0x5ef880 (preOf R a) (postOf R a) := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibDrs.program.link impl) := by
    rw [LibDrs.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDrs.names
  have hmc' : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R :=
    MemclrNoHeapPointersLive64.of_codeIn hc hmc
  exact Summary.induction_mutual (entry := fun _ => 0x5ef880) μ fun n ih a =>
    drs_step impl hap R ns hns hcode hmul hgr hmc hwb hmc' hmv n ih a

/-- **`divRecursiveStep` (amd64)**: `Q.DivLarge.DrsHypQ impl R drsCQ` (the premise of `divLarge` / `nat.div`), modulo
the `nat.mul` premise `MulHypQE` (divmc's export) and the live runtime contracts -/
theorem hyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (ns : List String) (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    DrsHypQ impl R drsCQ := by
  intro H b L qp ql qc st up ul uc d vp vl vc
  rw [show DivLarge.drsNames = LibDrs.names from rfl, ← LibDrs.eq_only, entry_drs]
  intro ret hret s hs hpre
  janus64_intro hs
  have hv9 := hpre.v9.1
  refine Summary.returns (sum impl hap R ns hns hcode hmul hgr hmc hwb hmv ⟨H, b, L, 40960, qp, ql, qc, st, up, ul, uc,
    d, vp, vl, vc⟩) hret (by rw [h_rip]) (by rw [retAddrOf, h_ret])
    ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6, h_a7⟩,
      drsW64_le hv9, hpre⟩
    fun s' h => by unfold postOf at h; obtain ⟨⟨a, b, c, d⟩, hq⟩ := h; exact ⟨⟨a, b, c, d⟩, hq⟩

end FvModexp.Amd64.Q.DivRec
