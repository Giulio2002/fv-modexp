import FvModexp.Proofs.Arm64.Nat.DrsFD2
import FvModexp.Proofs.Arm64.Nat.DrsD3

/-!
# `divRecursiveStep` (arm64), final block: `if e > 0 { panic }`, `subVV(u[:len(qhatv)], …, qhatv)` call (natdiv.go:881-884)

`d3F`: from `nat.cmp`'s return `0x1bac10`: the `panic("impossible")` branch is excluded by `he` (`e_leF`), the
`len(qhatv) ≤ cap(u)` check, the nine argument words → `CALL subVV.abi0` (`0x1bac48`, return `0x1bac4c`).
Adapted from DrsD3.
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the return address of the final `subVV.abi0(u[:ql], u[:ql], qhatv)` -/
abbrev rFD4 : Nat := 0x1bac4c

/-- `|PF| ≤ 2B ≤ n` -/
theorem PF_len_le2 {c : Cx} {s : State} {U : List Nat} (hB : 1 ≤ c.vl / 2) :
    (c.PF s U).length ≤ 2 * (c.vl / 2) := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := qF_len (c := c) (s := s) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d3F (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFD2) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.PF s U).length st))
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv4 : V3F c s T.mem qv (c.PF s U).length)
    (he : Mdl.cmpQ (c.PF s U).length st ≤ 0)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 subVVA → X.regs 30 = BitVec.ofNat 64 rFD4 →
      X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 →
      MemFrame T.mem X.mem (isA s) → X.mem.regions = T.mem.regions →
      X.mem.readLE (s.sp.toNat - 392) 8 = c.up → X.mem.readLE (s.sp.toNat - 384) 8 = (c.PF s U).length →
      X.mem.readLE (s.sp.toNat - 368) 8 = c.up → X.mem.readLE (s.sp.toNat - 344) 8 = qv →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hjB := hmc.jB
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl := PF_len_le2 (c := c) (s := s) (U := U) (by omega)
  have hPc : (c.PF s U).length ≤ c.uc := by have := hcr.vu1; omega
  have hc' : (BitVec.ofNat 64 c.uc).toNat = c.uc := by rw [BitVec.toNat_ofNat]; omega
  have hp' : (BitVec.ofNat 64 (c.PF s U).length).toNat = (c.PF s U).length := by
    rw [BitVec.toNat_ofNat]; omega
  have hle' : BitVec.ofNat 64 (c.PF s U).length ≤ BitVec.ofNat 64 c.uc := by
    rw [BitVec.le_def, hp', hc']; exact hPc
  have r1 := hv4.s320; have r2 := hv4.s144; have r3 := hv4.s160
  have r4 := hmc.bd.sl.s5; have r5 := hmc.bd.sl.s7
  have hqv : qv < 2 ^ 48 := by have := Memory.accessible_bound _ hmc.qa; omega
  obtain ⟨e1, e2, e3, e4⟩ := rd9 T.mem s.sp.toNat c.up (c.PF s U).length c.uc c.up
    (c.PF s U).length c.uc qv (c.PF s U).length (3 * c.vl) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  clear hmc hv4
  rcases natCmp_range (st.buf.take (c.PF s U).length) (Mdl.norm st.w) with hq | hq | hq
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
    have : Mdl.cmpQ (c.PF s U).length st = 1 := hq
    omega

end FvModexp.Arm64.DivRec
