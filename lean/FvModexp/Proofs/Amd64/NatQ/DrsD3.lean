import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsD3.lean)
# `divRecursiveStep` (amd64), after the correction loop: the `panic("impossible")` test → `CALL subVV.abi0` (natdiv.go:844-847)

`d3`: from `nat.cmp`'s return (`0x5eff71`) with `RAX = cmpQ |P| st ≤ 0` (`TESTQ; JG 0x5f0714` panic not taken) →
`uu[:len(qhatv)]` bounds check (`CMPQ AX, CX; JA 0x5f070f` excluded: `|P| ≤ cap uu`) → the nine argument words of
`subVV.abi0(uu[:ql], uu[:ql], qhatv)` at `0(SP') … 64(SP')` (`[r-392, r-320)`) → `CALL` (`0x5effd4`, return `0x5effd9`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d3 (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rD2) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st))
    (hmc : Mc R c s Lk bk T.mem j Z U qv st) (hv4 : V4 c s T.mem qv (c.P s j U).length)
    (he : Mdl.cmpQ (c.P s j U).length st ≤ 0)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 subVVA → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      MemFrame T.mem X.mem (isA s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rD4 →
      X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.uuP j → X.mem.readLE ((s.regs 4).toNat - 384) 8 = (c.P s j U).length →
      X.mem.readLE ((s.regs 4).toNat - 368) 8 = c.uuP j → X.mem.readLE ((s.regs 4).toNat - 344) 8 = qv →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, hu48, -, -, -⟩ := hpre.ua
  have hulc := hpre.ulc; have huc40 := hpre.uc40; have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl := P_len_le2 (c := c) (s := s) (j := j) (U := U) (by omega)
  have hPc : (c.P s j U).length ≤ c.uuC j := by simp only [Cx.uuC]; omega
  have hgt : (BitVec.ofNat 64 (c.uuC j) < BitVec.ofNat 64 (c.P s j U).length) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show c.uuC j < 2 ^ 64 by simp only [Cx.uuC]; omega),
      Nat.mod_eq_of_lt (show (c.P s j U).length < 2 ^ 64 by omega)]
    omega
  have r1 := hv4.s328; have r2 := hv4.s152; have r3 := hv4.s168
  have r4 := hmc.bd.sup; have r5 := hmc.bd.suc
  have hqv : qv < 2 ^ 48 := by have := Janus.Arm64.Memory.accessible_bound _ hmc.qa; omega
  have huP : c.uuP j < 2 ^ 48 := by simp only [Cx.uuP]; omega
  have huPe : c.uuP j = c.up + 8 * (j - c.vl / 2) := rfl
  have hucE : c.uuC j = c.uc - (j - c.vl / 2) := rfl
  clear hmc hv4 hpre hcr
  rcases natCmp_range (st.buf.take (c.P s j U).length) (Mdl.norm st.w) with hq | hq | hq
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
    have : Mdl.cmpQ (c.P s j U).length st = 1 := hq
    omega

end FvModexp.Amd64.Q.DivRec
