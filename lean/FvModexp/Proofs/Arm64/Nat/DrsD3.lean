import FvModexp.Proofs.Arm64.Nat.DrsD2
import FvModexp.Proofs.Arm64.Nat.DrsC4R

/-!
# `divRecursiveStep` (arm64), after the correction loop: the `panic("impossible")` test → `CALL subVV.abi0` (natdiv.go:844-847)

`d3`: from `nat.cmp`'s return (`0x1ba848`) with `X0 = cmpQ |P| st ≤ 0` (the caller supplies `e ≤ 0` from the model,
`e_le`) → `BGT` panic not taken → `uu[:len(qhatv)]` bounds check (`BHI` panic excluded: `|P| ≤ cap uu`) → the nine
argument words of `subVV.abi0(uu[:ql], uu[:ql], qhatv)` at `SP'+8 … SP'+72` → its call state (`0x1ba880`, `X30 = 0x1ba884`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- `|P| ≤ 2B ≤ n` -/
theorem P_len_le2 {c : Cx} {s : State} {j : Nat} {U : List Nat} (hB : 1 ≤ c.vl / 2) :
    (c.P s j U).length ≤ 2 * (c.vl / 2) := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d3 (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rD2) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st))
    (hmc : Mc R c s Lk bk T.mem j Z U qv st) (hv4 : V4 c s T.mem qv (c.P s j U).length)
    (he : Mdl.cmpQ (c.P s j U).length st ≤ 0)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 subVVA → X.regs 30 = BitVec.ofNat 64 0x1ba884 →
      X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 →
      MemFrame T.mem X.mem (isA s) → X.mem.regions = T.mem.regions →
      X.mem.readLE (s.sp.toNat - 392) 8 = c.uuP j → X.mem.readLE (s.sp.toNat - 384) 8 = (c.P s j U).length →
      X.mem.readLE (s.sp.toNat - 368) 8 = c.uuP j → X.mem.readLE (s.sp.toNat - 344) 8 = qv →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl := P_len_le2 (c := c) (s := s) (j := j) (U := U) (by omega)
  have hPc : (c.P s j U).length ≤ c.uuC j := by simp only [Cx.uuC]; omega
  have hc' : (BitVec.ofNat 64 (c.uuC j)).toNat = c.uuC j := by rw [BitVec.toNat_ofNat]; simp only [Cx.uuC]; omega
  have hp' : (BitVec.ofNat 64 (c.P s j U).length).toNat = (c.P s j U).length := by
    rw [BitVec.toNat_ofNat]; simp only [Cx.uuC] at hPc; omega
  have hle' : BitVec.ofNat 64 (c.P s j U).length ≤ BitVec.ofNat 64 (c.uuC j) := by
    rw [BitVec.le_def, hp', hc']; exact hPc
  have r1 := hv4.s328; have r2 := hv4.s152; have r3 := hv4.s168
  have r4 := hmc.bd.sup; have r5 := hmc.bd.suc
  have hqv : qv < 2 ^ 48 := by have := Memory.accessible_bound _ hmc.qa; omega
  obtain ⟨e1, e2, e3, e4⟩ := rd9 T.mem s.sp.toNat (c.uuP j) (c.P s j U).length (c.uuC j) (c.uuP j)
    (c.P s j U).length (c.uuC j) qv (c.P s j U).length (3 * c.vl) (by omega) (by simp only [Cx.uuP]; omega)
    (by omega) (by simp only [Cx.uuP]; omega) (by omega)
  clear hmc hv4
  rcases natCmp_range (st.buf.take (c.P s j U).length) (Mdl.norm st.w) with hq | hq | hq
  · have h0' : T.regs 0 = 18446744073709551615#64 := by
      rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [hq]; rfl
    janus_run [r1, r2, r3, r4, r5, h0'] until [subVVA]
    refine k _ rfl rfl rfl ?_ ?_ ?_ (by unfold isA; janus_frame) (by simp) e1 e2 e3 e4
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · have h0' : T.regs 0 = 0#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [hq]; rfl
    janus_run [r1, r2, r3, r4, r5, h0'] until [subVVA]
    refine k _ rfl rfl rfl ?_ ?_ ?_ (by unfold isA; janus_frame) (by simp) e1 e2 e3 e4
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · exfalso
    have : Mdl.cmpQ (c.P s j U).length st = 1 := hq
    omega

end FvModexp.Arm64.DivRec
