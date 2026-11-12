import FvModexp.Proofs.Amd64.Nat.BasicSqrPro3
import FvModexp.Proofs.Amd64.Nat.BasicSqrSmall
import FvModexp.Proofs.Amd64.Nat.StackNatDefs

/-!
# `basicSqr` (amd64): the large path's prologue — `defer stk.restore(stk.save())`, `t := stk.nat(2n)` (natmul.go:119-120;
the amd64 twin of `Arm64/Nat/BasicSqrPro.lean`)

`CALL (*stack).nat` at `+0xb9` (entry `RSP - 200`, return `+0xbe` = 6231390), then the spills of `t` (`RSP - 88` len,
`RSP - 48` ptr, `RSP - 80` cap) and `memclr`'s arguments up to `clr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.BasicSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem pro2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    (hmc : MemclrNoHeapPointersLive64 (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15s : s.xmm 15 = 0#128) (hdfs : s.df = false)
    (P : State) (hP : AtNat R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s P)
    (hinvP : R.inv b L (s.regs 14).toNat (view R.rt L P.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) P fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hc : CodeIn64 ((Extracted.program.onlySegments StackNat.names).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hSN' := fun b L => Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1)
    (A64.noExit_restrict64 hap StackNat.names) hc
  clear hc
  simp only [StackNat.Pre, CallEnv, TlsOK] at hSN'
  have hpc := hP.pc; have hsp := hP.sp; have h5 := hP.r5; have h14 := hP.r14; have hfs := hP.fs; have hx15 := hP.x15
  have hdf := hP.df; have r0 := hP.r0; have r3 := hP.r3; have hF := hP.fr; have hreg := hP.reg
  have p1 := hP.bp; have p2 := hP.dfn; have p3 := hP.dst; have p4 := hP.dn; have p5 := hP.dp; have p6 := hP.s1
  have p7 := hP.s2; have p8 := hP.s3; have p9 := hP.s4; have p10 := hP.s5; have p11 := hP.s6
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  simp only [LiveSep, win, outside_cons, outside_nil, and_true] at hLs
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 200 - 4192 ∨ (s.regs 4).toNat - 200 + 24 ≤ r.1 := by
    intro r hr; have := hLs r hr; omega
  clear hLs
  have hfw : s.fsBase.toNat - 8 + 8 ≤ (s.regs 4).toNat - 200 - 4192 ∨
      (s.regs 4).toNat - 200 - 4192 + 4216 ≤ s.fsBase.toNat - 8 := by unfold Apart at htw; omega
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 89 ∨ (s.regs 4).toNat + 64 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hPacc : ∀ a n v, P.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_frame64 hdl hreg hro (rt := R.rt) (hF.widen R.rt) (by
      intro r hr _; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega)
        (by simp only; omega))
  have hgP : P.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hrd _ _ (by unfold Apart at hga; omega)
  have htP : P.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [← htg]; exact hrd _ _ (by unfold Apart at htw; omega)
  have htP' : (P.mem.writeLE ((s.regs 4).toNat - 200) 8 6231390).readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
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
  have hn2 : 2 * xl.toNat % 18446744073709551616 = 2 * xl.toNat := Nat.mod_eq_of_lt (by simp only [stLen] at hlen; omega)
  have hcost := hpre.cost
  have hstarr := hpre.starr
  simp only [stW, stCap, stLen] at hlen hcost hstarr
  have hwbP : P.mem.accessible StackNat.wbA 4 false = true := by rw [hPacc]; exact hpre.wba
  have hstwb := hpre.stwb; unfold Apart at hstwb
  have hstfr := hpre.stfree; simp only [freeP, freeN, stW, stLen, stCap] at hstfr; unfold Apart at hstfr
  have hst24 : st.toNat < 2 ^ 64 := st.isLt
  have e200 : (s.regs 4 - 200#64).toNat = (s.regs 4).toNat - 200 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hws : stkWs (P.mem.writeLE ((s.regs 4).toNat - 200) 8 6231390) st.toNat = stkWs s.mem st.toNat := by
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
    janus64_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, hn2, hgP, htP', hfs] until [callNat + 5] calls [hSN' b L]
    rename_i hpc' hsp' h5' h14' hx15' hfs' hdf' hr3' hr1' L1 b1 hext hr0' hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame
      hgrow hF2 hLF2 hmem2
    simp only [win, Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e200, hws] at hF2 hLF2
    exact pro3 impl R hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hra hx15s hdfs P hP s'
      (by rw [hpc']; try janus64_simp) (by rw [hsp']; try janus64_simp) (by rw [h5']; try janus64_simp)
      (by rw [h14']; try janus64_simp) (by rw [hfs']) (by rw [hx15']; try exact hx15) (by rw [hdf']; try exact hdf)
      (hr0' (by omega)) (by rw [hr3']; try janus64_simp)
      (by rw [hr1']; try janus64_simp)
      L1 b1 hext hbud hinv2
      ⟨k1, k2, by rw [hF2.accessible, Janus.Arm64.Memory.accessible_writeLE, hPacc]; exact k3, by omega, k5, k6, k7⟩
      hlen2 hsame hgrow hmem2 hF2 hLF2
  · janus64_run [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, hn2, hgP, htP', hfs] until [callNat + 5] calls [hSN' b L]
    rename_i hpc' hsp' h5' h14' hx15' hfs' hdf' hr3' hr1' L1 b1 hext hr0' hbud hinv2 k1 k2 k3 k4 k5 k6 k7 hlen2 hsame
      hgrow hF2 hLF2 hmem2
    simp only [win, Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e200, hws] at hF2 hLF2
    exact pro3 impl R hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hra hx15s hdfs P hP s'
      (by rw [hpc']; try janus64_simp) (by rw [hsp']; try janus64_simp) (by rw [h5']; try janus64_simp)
      (by rw [h14']; try janus64_simp) (by rw [hfs']) (by rw [hx15']; try exact hx15) (by rw [hdf']; try exact hdf)
      (hr0' (by omega)) (by rw [hr3']; try janus64_simp)
      (by rw [hr1']; try janus64_simp)
      L1 b1 hext hbud hinv2
      ⟨k1, k2, by rw [hF2.accessible, Janus.Arm64.Memory.accessible_writeLE, hPacc]; exact k3, by omega, k5, k6, k7⟩
      hlen2 hsame hgrow hmem2 hF2 hLF2


end FvModexp.Amd64.BasicSqr
