import FvModexp.Proofs.Arm64.Nat.DrsSegD
import FvModexp.Proofs.Common.MaskWord
/-!
# `divRecursiveStep` (arm64), correction loop: `if len(qhatv) > s { subVW(qhatv[s:], qhatv[s:], c) }` test (natdiv.go:839)
`c5r`: from `subVV.abi0`'s return (`0x1ba7a8`): `len(qhatv) ≤ s` → the `addTo(uu[s:], v[s:])` call state (`0x1ba6e8`,
model `stC`, via `corrSub`'s `else`); `len(qhatv) > s` → the `CALL subVW(qhatv[s:], qhatv[s:], c)` state (`0x1ba7f0`).
-/
set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5r (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 0x1ba7a8)
    (hbx : Bx R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)))
    (hcy : T.mem.readLE (s.sp.toNat - 320) 8 =
      (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2)
    (kA : ∀ X : State, X.pc = BitVec.ofNat 64 addToA → X.regs 30 = BitVec.ofNat 64 0x1ba6ec →
      X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1)) → X.regs 1 = BitVec.ofNat 64 (c.u1 - j + 1) →
      X.regs 2 = BitVec.ofNat 64 (c.uc - j + 1) → X.regs 3 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
      X.regs 4 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1) → X.regs 5 = BitVec.ofNat 64 (c.vc - c.vl / 2 + 1) →
      Bx R c s Lk bk X j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q)
    (kW : ∀ Y : State, Y.pc = BitVec.ofNat 64 SubVW.entry → Y.regs 30 = BitVec.ofNat 64 0x1ba7f4 →
      Y.regs 0 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 1 = BitVec.ofNat 64 ((c.P s j U).length - c.vl / 2 + 1) →
      Y.regs 2 = BitVec.ofNat 64 (3 * c.vl - c.vl / 2 + 1) → Y.regs 3 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 4 = BitVec.ofNat 64 ((c.P s j U).length - c.vl / 2 + 1) →
      Y.regs 5 = BitVec.ofNat 64 (3 * c.vl - c.vl / 2 + 1) →
      Y.regs 6 = BitVec.ofNat 64 (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 →
      c.vl / 2 - 1 < (c.P s j U).length →
      Bx R c s Lk bk Y j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsp := hbx.sp; have h28 := hbx.r28; have h29 := hbx.r29; have h18 := hbx.r18
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have r1 := hbx.v4.s152; have r2 := hmc.bs.b1; have r3 := hbx.v4.s168; have r4 := hbx.v4.s328
  have r5 := hmc.bd.sl.nn; have r6 := hcy; have r7 := hmc.bd.sul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hsu : c.vl / 2 - 1 ≤ c.u1 - (j - c.vl / 2) := by omega
  have hu1 := hcr.u1ul
  have hub : c.u1 - (j - c.vl / 2) < 2 ^ 64 := by omega
  have r8 := hmc.bs.uptr; have r9 := hmc.bs.ucap; have r10 := hmc.bs.jj; have r11 := hmc.bs.vcap
  have r12 := hmc.bs.vlen; have r13 := hmc.bs.vptr; have r14 := hmc.bd.sl.ul'
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hqv : qv < 2 ^ 48 := by have := Memory.accessible_bound _ hmc.qa; omega
  have hPl : (c.P s j U).length ≤ 3 * c.vl := P_len_le (by omega)
  have hti := toInt_small (n := (c.P s j U).length) (by omega)
  have hju : j ≤ c.u1 := by omega
  have hv48 : c.vp + 8 * c.vl ≤ 2 ^ 48 := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hB1 : Box (Mc R c s Lk bk T.mem j Z U qv (stV (c.V s) (c.vl / 2 - 1) (stQ stb))) := ⟨hbx.mc⟩
  have hB2 : Box (V4 c s T.mem qv (c.P s j U).length) := ⟨hbx.v4⟩
  have hsi := hbx.si; have hi := hbx.hi; have hpos := hbx.pos; have hinv := hbx.inv
  have e1 := bvA hju (by omega : c.u1 < 2 ^ 64)
  have e2 := bvB (a := (c.P s j U).length) (n := c.vl)
  have e3 := bvB (a := 3 * c.vl) (n := c.vl) (by omega) (by omega) (by omega)
  have e4 := bvC (q := qv) (k := c.vl / 2 - 1) (x := 3 * c.vl - c.vl / 2 + 1) (by omega) (by omega) (by omega) (by omega)
  clear hbx hmc
  janus_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14] until [SubVW.entry, addToA]
  · -- `len(qhatv) ≤ s`: `addTo`
    have hle : ¬ c.vl / 2 - 1 < (c.P s j U).length := by omega
    refine kA _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ⟨rfl, ?_, ?_, ?_, stC_le hle ▸ hB1.1, hB2.1, hsi, hi, hpos, hinv⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact e1
    · exact h28
    · exact h29
    · exact h18
  · -- `len(qhatv) > s`: `subVW(qhatv[s:], qhatv[s:], c)`
    have hlt : c.vl / 2 - 1 < (c.P s j U).length := by omega
    have e2' := e2 (by omega) (by omega) (by omega)
    refine kW _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl hlt ⟨rfl, ?_, ?_, ?_, hB1.1, hB2.1, hsi, hi, hpos, hinv⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · rw [e3]; exact e4
    · exact e2'
    · exact e3
    · rw [e3]; exact e4
    · exact e2'
    · exact e3
    · exact h28
    · exact h29
    · exact h18

end FvModexp.Arm64.DivRec
