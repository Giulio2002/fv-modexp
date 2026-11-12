import FvModexp.Proofs.Amd64.Nat.DivBasicRel
import FvModexp.Proofs.Amd64.Nat.Callees2

set_option autoImplicit false

/-!
# `divBasic` (amd64): the call `qhatv := stk.nat(n + 1)` (natdiv.go:651)

`pro2`: from `AtNat` (state `P` at `CALL (*stack).nat`, `+0xaf`) through the call (premise `StackNat.HypL`, as in
divmc's amd64 `BasicSqr.pro2`), to the return point `+0xb4` with the post facts `AfterNat` handed to a continuation.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc : BitVec 64) (vp vl : Nat) (s : State)
    (hpre : Pre R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s)
    (P : State) (hP : AtNat R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s P)
    (hinvP : R.inv b L (s.regs 14).toNat (view R.rt L P.mem)) (Q : State → Prop)
    (k : ∀ S2 L1 b1, AfterNat R b L st.toNat vl s P S2 L1 b1 →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S2 Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) P Q := by
  have hc : CodeIn64 ((Extracted.program.onlySegments StackNat.names).link impl) (LibDivBasic.program.link impl) := by
    rw [LibDivBasic.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hSN' := fun b L => Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1)
    (A64.noExit_restrict64 hap StackNat.names) hc
  clear hc
  simp only [StackNat.Pre, CallEnv, TlsOK] at hSN'
  have hpc := hP.pc; have hsp := hP.sp; have h5 := hP.r5; have h14 := hP.r14; have hfs := hP.fs; have hx15 := hP.x15
  have hdf := hP.df; have r0 := hP.r0; have r3 := hP.r3; have hF := hP.fr; have hreg := hP.reg
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  simp only [LiveSep, win, outside_cons, outside_nil, and_true] at hLs
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 232 - 4192 ∨ (s.regs 4).toNat - 232 + 24 ≤ r.1 := by
    intro r hr; have := hLs r hr; omega
  clear hLs
  have hfw : s.fsBase.toNat - 8 + 8 ≤ (s.regs 4).toNat - 232 - 4192 ∨
      (s.regs 4).toNat - 232 - 4192 + 4216 ≤ s.fsBase.toNat - 8 := by unfold Apart at htw; omega
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 137 ∨ (s.regs 4).toNat + 88 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)
  have hPacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_frame64 hdl hreg hro (rt := R.rt) (hF.widen R.rt) (by
      intro r hr _; simp only [proWs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega)
        (by simp only; omega))
  have hgP : P.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hrd _ _ (by unfold Apart at hga; omega)
  have htP : P.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [← htg]; exact hrd _ _ (by unfold Apart at htw; omega)
  have htP' : (P.mem.writeLE ((s.regs 4).toNat - 232) 8 raNat).readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at htw; omega)]; exact htP
  have hstok := hpre.stok
  have hstO : StkOK P.mem R L st.toNat := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hstok
    simp only [StkOK, stW, stLen, stCap] at a5 a6 a7 ⊢
    rw [hrd st.toNat 8 (by omega), hrd (st.toNat + 8) 8 (by omega), hrd (st.toNat + 16) 8 (by omega), hPacc]
    refine ⟨a1, a2, a3, a4, ?_, a6, a7⟩
    intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hPacc]; exact b3, b4⟩
  have hsv := hpre.sv
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hstO
  have q2' : InRanges st.toNat 24 L ∨ Outside st.toNat 24 R.rt := q2
  simp only [NatLive, stW, stCap, stLen] at q5 q6 q7
  have hlen := hpre.stlen
  have eW : stW P.mem st.toNat = stW s.mem st.toNat := hrd _ _ (by omega)
  have eL : stLen P.mem st.toNat = stLen s.mem st.toNat := hrd _ _ (by omega)
  have eC : stCap P.mem st.toNat = stCap s.mem st.toNat := hrd _ _ (by omega)
  have hn2 : (vl + 1) % 18446744073709551616 = vl + 1 := Nat.mod_eq_of_lt (by simp only [stLen] at hlen; omega)
  have hcost := hpre.cost
  have hstarr := hpre.starr
  simp only [stW, stCap, stLen] at hlen hcost hstarr
  have hwbP : P.mem.accessible StackNat.wbA 4 false = true := by rw [hPacc]; exact hpre.wbacc
  have hstwb := hpre.wbap; unfold Apart at hstwb
  have hstfr := hpre.stfree; simp only [freeP, freeN, stW, stLen, stCap] at hstfr; unfold Apart at hstfr
  have hst24 : st.toNat < 2 ^ 64 := st.isLt
  have e232 : (s.regs 4 - 232#64).toNat = (s.regs 4).toNat - 232 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hws : stkWs (P.mem.writeLE ((s.regs 4).toNat - 232) 8 raNat) st.toNat = stkWs s.mem st.toNat := by
    simp only [stkWs, stW, stLen, stCap]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hrd _ _ (by omega), hrd _ _ (by omega),
      hrd _ _ (by omega)]
  by_cases hc0 : 0 < s.mem.readLE (st.toNat + 16) 8
  · have hnl := hpre.stok.2.2.2.2.1
    simp only [NatLive, stW, stCap] at hnl
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc0
    obtain ⟨a5, a6⟩ := hstarr hc0
    simp only [win, outside_cons, outside_nil, and_true] at a5
    unfold Apart at a6
    have a2' : InRanges (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) L ∨
      Outside (s.mem.readLE st.toNat 8) (8 * s.mem.readLE (st.toNat + 16) 8) R.rt := a2
    janus64_run [hn2, hgP, htP', hfs] until [callNat + 5] calls [hSN' b L]
    rename_i hpc' hsp' h5' h14' hx15' hfs' hdf' hr3' hr1' L1 b1 hext hr0' hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame
      hgrow hF2 hLF2 hmem
    simp only [win, Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e232, hws] at hF2 hLF2
    refine k s' L1 b1 ⟨?qpc, ?qsp, ?q5, ?q14, ?qfs, ?qx, ?qdf, hr0' (by omega), ?q3, ?q1, hext, by simpa using hbud, hinv2,
      ⟨k1, k2, by rw [hF2.accessible, Janus.Arm64.Memory.accessible_writeLE, hPacc]; exact k3, by omega, k5, k6, k7⟩,
      hlen2, hsame, hgrow, hF2, hLF2, hmem⟩
    case qpc => rw [hpc']; janus64_simp
    case qsp =>
      rw [hsp']; simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte]; bv_omega
    case q5 => rw [h5']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; try exact h5
    case q14 => rw [h14']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; try exact h14
    case qfs => rw [hfs']
    case qx => rw [hx15']; try exact hx15
    case qdf => rw [hdf']; try exact hdf
    case q3 => rw [hr3']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, r3, BitVec.toNat_ofNat, hn2]
    case q1 => rw [hr1']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, r3, BitVec.toNat_ofNat, hn2]
  · janus64_run [hn2, hgP, htP', hfs] until [callNat + 5] calls [hSN' b L]
    rename_i hpc' hsp' h5' h14' hx15' hfs' hdf' hr3' hr1' L1 b1 hext hr0' hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame
      hgrow hF2 hLF2 hmem
    simp only [win, Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e232, hws] at hF2 hLF2
    refine k s' L1 b1 ⟨?qpc, ?qsp, ?q5, ?q14, ?qfs, ?qx, ?qdf, hr0' (by omega), ?q3, ?q1, hext, by simpa using hbud, hinv2,
      ⟨k1, k2, by rw [hF2.accessible, Janus.Arm64.Memory.accessible_writeLE, hPacc]; exact k3, by omega, k5, k6, k7⟩,
      hlen2, hsame, hgrow, hF2, hLF2, hmem⟩
    case qpc => rw [hpc']; janus64_simp
    case qsp =>
      rw [hsp']; simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte]; bv_omega
    case q5 => rw [h5']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; try exact h5
    case q14 => rw [h14']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; try exact h14
    case qfs => rw [hfs']
    case qx => rw [hx15']; try exact hx15
    case qdf => rw [hdf']; try exact hdf
    case q3 => rw [hr3']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, r3, BitVec.toNat_ofNat, hn2]
    case q1 => rw [hr1']; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, r3, BitVec.toNat_ofNat, hn2]

end FvModexp.Amd64.DivBasic
