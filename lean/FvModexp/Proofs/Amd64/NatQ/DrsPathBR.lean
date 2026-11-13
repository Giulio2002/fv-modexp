import FvModexp.Proofs.Amd64.NatQ.DrsPathB

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the run of the `divBasic` path (`n < 40`, `0 < len u`) (natdiv.go:762-765)

From the dispatch: `TESTQ R8, R8` (not taken), `CMPQ divRecursiveThreshold, R11; JG 0x5efa08` (taken: `40 > n`),
`MOVQ DX, 0(SP); MOVQ R11, 8(SP); MOVQ R12, 16(SP)` (`v`'s stack arguments), `CALL nat.divBasic` (return site
`0x5efa1b`), then the epilogue `epB`. `callB`: from `divBasic`'s entry (abstract state `S`) through the call to the
return; `pathB`: the run to the call. Twin of Arm64/NatQ/DrsPathBR.lean.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem tN64B {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the stack pointer after the callee's `RET` -/
theorem sp_retB {x y : BitVec 64} (h : x.toNat = y.toNat - 400) (hy : 400 ≤ y.toNat) : x + 8#64 = y - 392#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega), h]
  simp only [BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- from `divBasic`'s entry `S` (`RSP = r - 400`): the call and the epilogue at `epB` -/
theorem callB (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp a.vl a.vc s) (hW : 4824 ≤ a.W) (ul' : Nat) (hle : ul' ≤ a.ul.toNat)
    (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat) (hN : NatNorm s.mem a.up.toNat ul')
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program FvModexp.Amd64.DivBasic.fn))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    (hdf : S.df = false) (hx15 : S.xmm 15 = 0#128) (hreg : S.mem.regions = s.mem.regions)
    (hF : MemFrame s.mem S.mem (fw s)) (hrd : S.mem.readLE ((s.regs 4).toNat - 400) 8 = 0x5efa1b)
    (hvS : S.mem.readLE ((s.regs 4).toNat - 392) 8 = a.vp) (hlS : S.mem.readLE ((s.regs 4).toNat - 384) 8 = a.vl)
    (hra' : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r0 : S.regs 0 = BitVec.ofNat 64 a.qp.toNat) (r3 : S.regs 3 = BitVec.ofNat 64 a.ql.toNat)
    (r7 : S.regs 7 = BitVec.ofNat 64 a.st.toNat) (r6 : S.regs 6 = BitVec.ofNat 64 a.up.toNat)
    (r8 : S.regs 8 = BitVec.ofNat 64 ul') (r9 : S.regs 9 = BitVec.ofNat 64 a.uc.toNat) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp a.vl s s') := by
  have hce := hpre.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hce
  simp only [regSP] at hb' ha hw
  have huc := hpre.uc40
  have eu : (BitVec.ofNat 64 ul').toNat = ul' := tN64B (by omega)
  obtain ⟨hra, hsx, hdf0, -⟩ := hE
  refine ReachesRet.call_regions (dbsum impl hap R hgr hmc hwb a.Hq a.b a.L a.vp a.vl) hpc
    ⟨?ra, hx15, hdf, ?pre⟩ fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_
  case ra => simp only [regSP]; rw [hsp, hrd]; exact raB impl hap
  case pre =>
    rw [r0, r3, r7, r6, r8, r9, bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat, eu]
    exact db_pre hpre hW hF hsp h14 hfs hreg hle hU hN hvS hlS
  rw [r0, r3, r7, r6, r8, bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat, eu] at hq
  have hsl := fun a' n (h1 : (s.regs 4).toNat - 312 ≤ a') (h2 : a' + n ≤ (s.regs 4).toNat + 96) =>
    db_slot (a := a') (n := n) hpre hW hF hsp hle hq h1 h2
  have hfsT := hq.1
  have hdfT := hq.2.1
  have hT4 : T.regs 4 = s.regs 4 - 392#64 := by
    rw [f4]; exact sp_retB hsp (by omega)
  refine epi impl s T epB (Or.inr (Or.inl rfl)) ?pc hT4 (by rw [f14, h14]) (by rw [hfsT, hfs])
    (by rw [hdfT, hdf]) ?hra2 ?hbp2 ?hx2 hdf0 hra (by omega) (by omega) ?acc _
    fun s' ⟨e1, e2, e3, e4⟩ => ⟨e1, db_post hpre hW hF hsp h14 hle hU hq e4 e2 e3⟩
  case pc => rw [hT, retAddrOf, hsp, hrd]
  case hra2 => rw [(hsl _ 8 (by omega) (by omega)).1]; exact hra'
  case hbp2 => rw [(hsl _ 8 (by omega) (by omega)).1]; exact hbp
  case hx2 => rw [f15, hx15, hsx]
  case acc =>
    rw [(hsl ((s.regs 4).toNat - 8) 16 (by omega) (by omega)).2]
    exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`n < divRecursiveThreshold`** (`0 < len u`): `z.divBasic(stk, u, v)`, return at `epB` -/
theorem pathB (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp a.vl a.vc s) (hW : 4824 ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp a.vl a.vc a.d.toNat)
    (hle : ul' ≤ a.ul.toNat) (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat)
    (hN : NatNorm s.mem a.up.toNat ul') (h0 : 0 < ul') (h40 : a.vl < 40) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp a.vl s s') := by
  have hce := hpre.ce
  have hgl := hpre.gl
  have hulc := hpre.ulc
  have huc := hpre.uc40
  have hE' := hE
  obtain ⟨-, -, hdf, -⟩ := hE'
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, -, hth, -, -, -, hgacc, -, hgw, -⟩ := hgl
  have eg : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» = 0xb4ae88 := rfl
  simp only [RunIface.gA, eg, win, outside_cons, outside_nil, and_true] at hgw hgacc hth
  have hF := hA.fr
  have hth' : P.mem.readLE 0xb4ae88 8 = 40 := by
    rw [hF.fr.readLE _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)]; exact hth
  have hthA : P.mem.accessible 0xb4ae88 8 false = true := by
    rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)
  have h8 := hA.r8
  have h11 := hA.r11
  have hne : (BitVec.ofNat 64 ul' = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hpc := hA.pc
  have hx0 := hA.x15
  have hsp0 := hF.sp
  have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp0, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hPacc : P.mem.accessible ((s.regs 4).toNat - 400) 400 true = true := by
    rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  janus64_run [h8, h11, hth', hne, BitVec.msb_eq_decide] until [segAddr Extracted.program FvModexp.Amd64.DivBasic.fn]
  have hv48 := hpre.va.2.1
  have e400 : (s.regs 4 - 400#64).toNat = (s.regs 4).toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hr2 : (P.regs 2).toNat = a.vp := by rw [hA.r2, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine callB impl hap R hgr hmc hwb a s hE hpre hW ul' hle hU hN _ rfl ?sp ?r14 hF.fs hF.df hx0 ?reg ?fr ?rd ?vS ?lS
    ?ra ?bp ?q0 ?q3 ?q7 ?q6 ?q8 ?q9
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, ite_true]; exact e400
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hF.r14
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hF.reg
  case fr => exact mf_trans hF.fr (by unfold fw win; janus_frame)
  case rd => exact Janus.Arm64.Memory.readLE_writeLE_self _ _ _ _
  case vS =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, hr2]
    exact Nat.mod_eq_of_lt (by omega)
  case lS =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := hpre.v9; omega)
  case ra =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hF.ra
  case bp =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hF.bp
  all_goals simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case q0 => exact hA.r0
  case q3 => exact hA.r3
  case q7 => exact hA.r7
  case q6 => exact hA.r6
  case q8 => exact hA.r8
  case q9 => exact hA.r9

end FvModexp.Amd64.Q.DivRec
