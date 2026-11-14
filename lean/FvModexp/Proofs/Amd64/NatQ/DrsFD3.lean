import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFD3.lean; adapted from Amd64/NatQ/DrsD3.lean)
# `divRecursiveStep` (amd64), final block: `if e > 0 { panic }`, `subVV(u[:len(qhatv)], …, qhatv)` call (natdiv.go:879-882)

`d3F`: from `nat.cmp`'s return (`0x5f0554`) with `RAX = cmpQ |PF| st ≤ 0` (`TESTQ; JG 0x5f06c5` panic not taken) →
`u[:len(qhatv)]` bounds check (`CMPQ AX, CX; JA 0x5f06be` excluded: `|PF| ≤ cap u`) → the nine argument words of
`subVV.abi0(u[:ql], u[:ql], qhatv)` at `0(SP') … 64(SP')` (`[r-392, r-320)`) → `CALL` (`0x5f05ba`, return `0x5f05bf`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d3F (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rFD2) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.PF s U).length st))
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv4 : V3F c s T.mem qv (c.PF s U).length)
    (he : Mdl.cmpQ (c.PF s U).length st ≤ 0)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 subVVA → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      MemFrame T.mem X.mem (isA s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFD4 →
      X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.up → X.mem.readLE ((s.regs 4).toNat - 384) 8 = (c.PF s U).length →
      X.mem.readLE ((s.regs 4).toNat - 368) 8 = c.up → X.mem.readLE ((s.regs 4).toNat - 344) 8 = qv →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, hu48, -, -, -⟩ := hpre.ua
  have hulc := hpre.ulc; have huc40 := hpre.uc40; have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl := PF_len_le2 (c := c) (s := s) (U := U) (by omega)
  have hPc : (c.PF s U).length ≤ c.uc := by omega
  have hgt : (BitVec.ofNat 64 c.uc < BitVec.ofNat 64 (c.PF s U).length) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show c.uc < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (c.PF s U).length < 2 ^ 64 by omega)]
    omega
  have r1 := hv4.s320; have r2 := hv4.s144; have r3 := hv4.s160
  have r4 := hmc.bd.sl.s5; have r5 := hmc.bd.sl.s7
  have hqv : qv < 2 ^ 48 := by have := Janus.Arm64.Memory.accessible_bound _ hmc.qa; omega
  have huP : c.up < 2 ^ 48 := by omega
  clear hmc hv4 hpre hcr
  rcases natCmp_range (st.buf.take (c.PF s U).length) (Mdl.norm st.w) with hq | hq | hq
  · have h0' : T.regs 0 = 18446744073709551615#64 := by
      rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [hq]; rfl
    janus64_run [r1, r2, r3, r4, r5, h0', hgt, BitVec.msb_eq_decide] until [subVVA]
    refine k _ rfl ?sp ?r5 ?r14 hfs rfl (by unfold isA; janus_frame) (by janus64_simp) ?ra ?e1 ?e2 ?e3 ?e4
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case r5 => exact h5
    case r14 => exact h14
    all_goals (try dsimp only)
    all_goals (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  · have h0' : T.regs 0 = 0#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [hq]; rfl
    janus64_run [r1, r2, r3, r4, r5, h0', hgt, BitVec.msb_eq_decide] until [subVVA]
    refine k _ rfl ?zsp ?zr5 ?zr14 hfs rfl (by unfold isA; janus_frame) (by janus64_simp) ?zra ?ze1 ?ze2 ?ze3 ?ze4
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case zr5 => exact h5
    case zr14 => exact h14
    all_goals (try dsimp only)
    all_goals (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  · exfalso
    have : Mdl.cmpQ (c.PF s U).length st = 1 := hq
    omega

end FvModexp.Amd64.Q.DivRec
