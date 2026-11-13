import FvModexp.Proofs.Amd64.NatQ.DrsSNH
import FvModexp.Proofs.Amd64.NatQ.DrsNat

set_option autoImplicit false

/-! (amd64 twin of Arm64/NatQ/DrsSN.lean, asm s45)
# `divRecursiveStep` (amd64), big path: `qhat0 := stk.nat(B + 1)` (`CALL 0x5ef9d8`) → the loop head (`H` at `j = m`)

`CALL (*stack).nat` (`snSum` on `LibDrs`, return `0x5ef9dd`), then `MOVQ AX, 0x148(SP); MOVQ CX, 0xa8(SP);
MOVQ BX, 0xa0(SP)` (`qhat0` at `r - 64 / - 224 / - 232`), `MOVQ 0xb0(SP), DX` (`j = m`), `JMP` to the head `0x5efa5f`.
`callN`: from the callee entry (abstract `S`); `snH`: from `AtN0` (the call instruction).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem tNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the `Cx` of an activation -/
@[reducible] def cOf (a : Args) (u1 t0 : Nat) (L1 : List (Nat × Nat)) : Cx :=
  ⟨a.Hq, a.b, a.L, a.W, a.qp.toNat, a.ql.toNat, a.qc.toNat, a.st.toNat, a.up.toNat, a.ul.toNat, a.uc.toNat, a.vp,
    a.vl, a.vc, a.d.toNat, u1, t0, L1⟩

/-- a range outside `rt ++ [(a, b)] ++ ws` is outside a sub-range of `[a, b)` -/
theorem out_sub {x k r : Nat} {S : State} {rt ws : List (Nat × Nat)} (hp : (S.regs 4).toNat = r - 400) (hr : 400 ≤ r)
    (ho : Outside x k (rt ++ win S 4192 24 ++ ws)) : Outside x k [(r - 400, r - 392)] := by
  rw [win, hp] at ho
  simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega

/-- the stack pointer after the callee's `RET` -/
theorem sp_retN {x y : BitVec 64} (h : x.toNat = y.toNat - 400) (hy : 400 ≤ y.toNat) : x + 8#64 = y - 392#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega), h]
  simp only [BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `(*stack).nat`'s entry `S` (`RSP = r - 400`): the call, then to the loop head with `j = m` -/
theorem callN (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (a : Args) (s : State) (hE : Entry a s)
    (hpre : DrsPreW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl) a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat
      a.up.toNat a.ul.toNat a.uc.toNat a.vp a.vl a.vc s)
    (hW : drsW64 a.vl ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtN0 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp a.vl a.vc a.d.toNat)
    (hle : ul' ≤ a.ul.toNat) (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat)
    (hN : NatNorm s.mem a.up.toNat ul') (h40 : 40 ≤ a.vl) (hvu : a.vl ≤ ul')
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 400) (h5 : S.regs 5 = s.regs 4 - 8#64) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hx15 : S.xmm 15 = 0#128) (hreg : S.mem.regions = s.mem.regions)
    (hPS : MemFrame P.mem S.mem [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392)])
    (hrd : S.mem.readLE ((s.regs 4).toNat - 400) 8 = 0x5ef9dd)
    (r0 : S.regs 0 = BitVec.ofNat 64 a.st.toNat) (r3 : S.regs 3 = BitVec.ofNat 64 (a.vl / 2 + 1)) (Q : State → Prop)
    (k : ∀ t0 L1 Lk bk S', H R (cOf a ul' t0 L1) s Lk bk S' (ul' - a.vl) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hWg := drsW64_ge a.vl
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hst48 := hpre.sti.1.2.2.2.1
  have hF := hA.fr
  have hF0 : MemFrame s.mem S.mem (fw s) := mf_trans hF.fr (hPS.mono fun x k ho => by
    simp only [fw, win, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hn64 : a.vl / 2 + 1 < 2 ^ 64 := by omega
  have h400 : 400 ≤ (s.regs 4).toNat := by omega
  have hsto : Outside a.st.toNat 24 (win s a.W 96) := hpre.sti.2.1
  have hfwo : Outside (stW s.mem a.st.toNat + 8 * stLen s.mem a.st.toNat)
      (8 * (stCap s.mem a.st.toNat - stLen s.mem a.st.toNat)) (win s a.W 96) := hpre.fw
  have hst : Outside a.st.toNat 24 (fw s) := by
    have h := hsto; simp only [win, fw, outside_cons, outside_nil, and_true] at h ⊢; omega
  have eW : stW S.mem a.st.toNat = stW s.mem a.st.toNat := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eL : stLen S.mem a.st.toNat = stLen s.mem a.st.toNat := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap S.mem a.st.toNat = stCap s.mem a.st.toNat := hF0.readLE _ _ (hst.of_sub (by omega) (by omega))
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hF0.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  refine ReachesRet.call_regions (snSum impl hap R hgr hmc hwb a.Hq a.b a.L) hpc ⟨?ra, hx15, hdf, ?pre⟩
    fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_
  case ra => simp only [regSP]; rw [hsp, hrd]; exact raS impl hap
  case pre =>
    rw [r0, r3, bv_ofNat_toNat, tNat hn64]
    exact sn_pre hpre (by omega) hF0 hsp h14 hfs hreg hv9
  rw [r0, r3, bv_ofNat_toNat, tNat hn64] at hq
  obtain ⟨hfsT, hdfT, hq0, hq3, hq1, L', b', ⟨hext, hbud, hinv⟩, hok, hlen, hsame, hgrow, hMF, hLF, hmem⟩ := hq
  -- the frame from the call state `P`
  have hMFP : MemFrame P.mem T.mem (R.rt ++ win S 4192 24 ++ stkWs S.mem a.st.toNat) :=
    mf_trans (hPS.mono fun x k ho => out_sub hsp h400 ho) hMF
  have hfo : FixOut s (R.rt ++ win S 4192 24 ++ stkWs S.mem a.st.toNat) := by
    refine fixOut_callee hpre.ce.2.2.2.2.1 (by omega) (by omega) hsp (by omega) ?_
    simp only [stkWs, eW, eL, eC]
    simp only [win, outside_cons, outside_nil, and_true] at hsto hfwo
    simp only [FixOut, outside_cons, outside_nil, and_true]; omega
  have hmmT : T.mem.readLE ((s.regs 4).toNat - 216) 8 = ul' - a.vl := by
    rw [hMFP.readLE _ _ (hfo.2.1.of_sub (by omega) (by omega))]; exact hA.mm
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by rw [hMF.accessible]; exact hSacc
  have hTpc : T.rip = BitVec.ofNat 64 0x5ef9dd := by rw [hT, retAddrOf, hsp, hrd]
  have hT4 : T.regs 4 = s.regs 4 - 392#64 := by rw [f4]; exact sp_retN hsp (by omega)
  have hT0 := hq0 (by omega)
  have hregT : T.mem.regions = s.mem.regions := by rw [hrg]; exact hreg
  have hinv' : R.inv b' L' (s.regs 14).toNat (view R.rt L' T.mem) := by rw [← h14]; exact hinv
  obtain ⟨hcr, hev, hfp, hkeep⟩ := hd_mem (c := cOf a ul' (stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat) L')
    (T := T.mem) (bk := b') hpre hE.1 hE.2.1 hE.2.2.1 hW h40 hvu hle hU hN hMF hLF hF0 hsp (by simp only [cOf])
    hext hinv' hok hlen hsame hgrow hmem hregT
  have hT0' : T.regs 0 = BitVec.ofNat 64 (stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat) := by rw [hT0, eL]
  have hb1 : a.b - stkR a.Hq s.mem a.st.toNat + stkR a.Hq T.mem a.st.toNat ≤ b' := by
    have := hbud; rw [stkR_congr eC] at this; exact this
  have ht48 : stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat + 8 * (a.vl / 2 + 1) ≤ 2 ^ 48 := hcr.t048
  clear f4 hT0 hext hinv hinv' hok hlen hsame hgrow hLF hmem hbud hrg hT hpre hMF hF0 hPS
  janus64_run [hmmT, hT0', hq3, hq1] until [head]
  refine k (stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat) L' L' b' _ ?_
  refine head_mk hcr hev hfp hkeep hA hMFP hfo hb1 rfl ?sp ?r5 ?r14 ?fs ?df ?x15 ?r0 ?r3 ?r1 ?r2
    (by janus_frame) (by janus64_simp) ?q1 ?q2 ?q3
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hT4
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [f5]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [f14]; exact h14
  case fs => change T.fsBase = s.fsBase; exact hfsT.trans hfs
  case df => rfl
  case x15 => change T.xmm 15 = 0#128; exact f15.trans hx15
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hT0'
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hq3
  case r1 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hq1
  case r2 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case q1 => rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  case q2 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]
  case q3 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`qhat0 := stk.nat(B + 1)`, then to the loop head** with `j = m` (from the call instruction, `AtN0`) -/
theorem snH (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (a : Args) (s : State) (hE : Entry a s)
    (hpre : DrsPreW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl) a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat
      a.up.toNat a.ul.toNat a.uc.toNat a.vp a.vl a.vc s)
    (hW : drsW64 a.vl ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtN0 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp a.vl a.vc a.d.toNat)
    (hle : ul' ≤ a.ul.toNat) (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat)
    (hN : NatNorm s.mem a.up.toNat ul') (h40 : 40 ≤ a.vl) (hvu : a.vl ≤ ul') (Q : State → Prop)
    (k : ∀ t0 L1 Lk bk S', H R (cOf a ul' t0 L1) s Lk bk S' (ul' - a.vl) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P Q := by
  have hWg := drsW64_ge a.vl
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hF := hA.fr
  have hpc := hA.pc
  have hx0 := hA.x15
  have hsp0 := hF.sp
  have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp0, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hPacc : P.mem.accessible ((s.regs 4).toNat - 400) 400 true = true := by
    rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have e400 : (s.regs 4 - 400#64).toNat = (s.regs 4).toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  janus64_run until [segAddr Extracted.program StackNat.fn]
  refine callN impl hap R hgr hmc hwb a s hE hpre hW P ul' hA hle hU hN h40 hvu _ ?pc ?sp ?r5 ?r14 ?fs ?df ?x15
    ?reg ?fr ?rd ?q0 ?q3 Q k
  case pc => rfl
  case fs => exact hF.fs
  case df => exact hF.df
  case x15 => exact hx0
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, ite_true]; exact e400
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hF.r5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hF.r14
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hF.reg
  case fr => janus_frame
  case rd => exact Janus.Arm64.Memory.readLE_writeLE_self _ _ _ _
  case q0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hA.r0
  case q3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hA.r3

end FvModexp.Amd64.Q.DivRec
