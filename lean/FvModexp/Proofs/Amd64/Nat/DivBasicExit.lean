import FvModexp.Proofs.Amd64.Nat.DivBasicEnd
import FvModexp.Proofs.Amd64.Nat.DivBasicCallees

set_option autoImplicit false

/-!
# `divBasic` (amd64): the loop exit (`TESTQ DX, DX; JL` taken at the head) through the deferred closure to the return

`head → +0x529`: `MOVB $0, 0x57(SP)` (defer bit, `RSP-137`), `RDX = 0xd0(SP)` (`&{deferwrap1, stk, len}` = `RSP-40`),
`RAX = (RDX)`, `callD = +0x539: CALL AX` (`deferwrap1` = `stk.restore`, `dsum`), `ADDQ $0xd8, SP; POPQ BP; RET`.
The twin of `Arm64/Nat/DivBasicExit.lean` (cf. `Amd64/Nat/BasicSqrEnd.lean` `fin4`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

/-- the closure call `CALL AX` (return `+0x53b` = 6223643) -/
abbrev callD : Nat := segAddr Extracted.program fn + 0x539

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem exitRun (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State) (sp r2 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 head) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (h2 : S.regs 2 = BitVec.ofNat 64 r2) (hneg : 2 ^ 63 ≤ r2) (hr2 : r2 < 2 ^ 64)
    (m16 : S.mem.readLE (sp - 16) 8 = sp - 40) (m40 : S.mem.readLE (sp - 40) 8 = dfnA)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 callD → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 2 = BitVec.ofNat 64 (sp - 40) → S'.regs 0 = BitVec.ofNat 64 dfnA →
      S'.mem = S.mem.writeLE (sp - 137) 1 0 → S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = S.df →
      ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e16 : S.mem.readLE ((S.regs 4).toNat + 208) 8 = sp - 40 := by
    rw [show (S.regs 4).toNat + 208 = sp - 16 by omega]; exact m16
  have e40 : S.mem.readLE (sp - 40) 8 = dfnA := m40
  have hmsb : (BitVec.ofNat 64 r2).msb = true := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hsm : (sp - 40) % 18446744073709551616 = sp - 40 := Nat.mod_eq_of_lt (by omega)
  janus64_run [h2, e16, e40, hmsb, hsm] until [callD]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
  · janus64_simp
  all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  show Arm64.Memory.writeLE S.mem _ 1 0 = _
  rw [show (S.regs 4).toNat + 87 = sp - 137 by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
/-- from the head with `RDX < 0` (no iteration left) through the closure and the epilogue to the return -/
theorem fin (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (r2 ujn : Nat)
    (hH : Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S r2 ujn) (hneg : 2 ^ 63 ≤ r2) (hr2 : r2 < 2 ^ 64)
    (hq : vl ≤ ul → natVal S.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl)
    (hu : natVal S.mem up ul = natVal s.mem up ul % natVal s.mem vp vl) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S (RQ R b L qp ql st up ul vp vl s) := by
  have hE := hH.env; have hM := hH.mem
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hsw := hl.sw
  have hpre := hE.pre
  have hw : s.mem.accessible ((s.regs 4).toNat - 4424) (4424 + 88) true = true := hpre.ce.2.1.2.2
  obtain ⟨hst8, -, hstacc, hst48, -, -, -⟩ := hpre.stok
  have hc1 := hE.c1len
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hsp : (S.regs 4).toNat + 224 = (s.regs 4).toNat := by
    rw [hH.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  refine exitRun impl _ _ S (s.regs 4).toNat r2 hH.pc hsp hsp0 hsp1 (by rw [hMacc]; exact hw) hH.r2 hneg hr2 hM.dp
    hM.dfn ?_
  intro E e0 e4 e5 e14 e2 e0' em ex efs edf
  have hFE : MemFrame S.mem E.mem [((s.regs 4).toNat - 137, (s.regs 4).toNat - 136)] := by
    rw [em]; exact MemFrame.of_writeLE _ _ (List.mem_singleton_self _) (Nat.le_refl _) (by omega)
  have rdE : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 137 ∨ (s.regs 4).toNat - 136 ≤ a) → E.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a h => hFE.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have e1 := (rdE _ (by omega)).trans hM.ra
  have e2' := (rdE _ (by omega)).trans hM.bp
  have hEacc : ∀ a n w, E.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hFE.accessible, hMacc]
  have hD := dsum impl
  have hstaccE : E.mem.accessible st 24 true = true := by rw [hEacc]; exact hstacc
  have hraccE : E.mem.accessible ((s.regs 4).toNat - 32) 16 false = true := by
    rw [hEacc]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  have hwaccE : E.mem.accessible ((s.regs 4).toNat - 240) 16 true = true := by
    rw [hEacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have f8 : E.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = st := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega, rdE _ (by omega)]; exact hM.dst
  have f16 : E.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 = stLen s.mem st := by
    rw [show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega, rdE _ (by omega)]; exact hM.dn
  have ecap : E.mem.readLE (st + 16) 8 = c1 := by
    rw [rdE _ (by omega)]; exact hM.hcap
  have hra := hE.ra
  have hsp2 : E.regs 4 = s.regs 4 - 224#64 := e4.trans hH.sp
  have h5 : E.regs 5 = s.regs 4 - 8#64 := e5.trans hH.r5
  have hx15 : E.xmm 15 = 0#128 := by rw [ex]; exact hH.x15
  have hfs : E.fsBase = s.fsBase := efs.trans hH.fs
  have h14 : E.regs 14 = s.regs 14 := e14.trans hH.r14
  clear hpre em
  have e0d : E.regs 0 = 6223936#64 := by rw [e0']
  have hsm : ((s.regs 4).toNat - 40) % 18446744073709551616 = (s.regs 4).toNat - 40 := Nat.mod_eq_of_lt (by omega)
  clear e0'
  have hSa : (S.regs 4).toNat % 8 = 0 := by have := hl.spa; omega
  have hraS : S.mem.readLE ((S.regs 4).toNat + 224) 8 < 2 ^ 47 := by
    rw [show (S.regs 4).toNat + 224 = (s.regs 4).toNat by omega, hM.ra]; exact hE.ra
  have eR : S.mem.readLE ((S.regs 4).toNat + 224) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [show (S.regs 4).toNat + 224 = (s.regs 4).toNat by omega, hM.ra]
  have hpopE : E.mem.accessible ((S.regs 4).toNat + 216) 16 false = true := by
    rw [hEacc, show (S.regs 4).toNat + 216 = (s.regs 4).toNat - 8 by omega]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  show ReachesRet _ (BitVec.ofNat 64 (s.mem.readLE (s.regs 4).toNat 8)) _ _
  janus64_run [e2, e0d, e1, e2', f8, f16, ecap, hsm, eR] calls [hD]
  rename_i _ h4' h5' h14' hx' hfs' hdf' hlen hFF
  have hFF' : MemFrame E.mem s'.mem (wsF (s.regs 4).toNat st) :=
    MemFrame.trans (MemFrame.of_writeLE (rs := [((S.regs 4).toNat - 8, (S.regs 4).toNat)]) E.mem 6223643
      (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)) hFF fun a n h => by
        simp only [wsF, outside_cons, outside_nil, and_true] at h ⊢; omega
  simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] at h14' hx' hfs'
  refine ⟨⟨?_, ?_, ?_, ?_⟩, post_fin hE hM hq hu hFE hFF' hlen _ rfl (hfs'.trans hfs) (by rw [hH.df, hE.df0])⟩
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [hH.sp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [show (S.regs 4).toNat + 216 = (s.regs 4).toNat - 8 by omega, hM.bp]; simp
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [h14', h14]
  · show s'.xmm 15 = _; rw [hx', hx15, hE.x15]

end FvModexp.Amd64.DivBasic
