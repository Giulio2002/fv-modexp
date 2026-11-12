import FvModexp.Proofs.Arm64.Nat.DivMJoin

set_option autoImplicit false

/-!
# `nat.div` (arm64), `stk == nil`: the epilogue after `divLarge` with the deferred `stk.free()` (natdiv.go:543-544)

`epiCD`: from `divLarge`'s return `retL` (`SP' = SP - 240`): the result stores (`[SP - 56, SP - 32)` = X0..X2,
`SP - 80 … SP - 64` = X3..X5), the defer bit test (`SP - 122` = 1: `TBZ` not taken), `MOVB ZR, SP - 121`,
`R26 := (SP - 16)` (= `SP - 32`, the closure record), `R0 := (R26)` (= `nat.div.deferwrap1`), `CALL (R0)` — stops at
the closure entry (`X30` = `fn + 0x2fc` = 1807612). `epiRD`: the closure call (any `Summary` of `deferwrap1` on
`LibDiv`), the result reloads, `LDP`, `RET`. Continuation form (as agent expmc's `ExpN.epi1s/epi1c/epi1r`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

/-- the return point of the closure call (fn + 0x2fc) -/
abbrev dwRD : Nat := 1807612

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- result stores, defer-bit test, closure call: `retL` → `deferwrap1`'s entry -/
theorem epiCD (impl : List Segment) {s : State} (Q : State → Prop)
    (hal : s.sp.toNat % 16 = 0) (hb' : 41504 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 retL) (hsp : T.sp = s.sp - 240#64)
    (hacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true)
    (mfl : T.mem.readLE (s.sp.toNat - 122) 1 = 1) (mrc : T.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32)
    (mdw : T.mem.readLE (s.sp.toNat - 32) 8 = dwD)
    (k : ∀ S2 : State, S2.pc = BitVec.ofNat 64 dwD → S2.sp = T.sp →
      S2.regs 26 = BitVec.ofNat 64 (s.sp.toNat - 32) → S2.regs 30 = BitVec.ofNat 64 dwRD →
      S2.regs 18 = T.regs 18 → S2.regs 28 = T.regs 28 → S2.regs 29 = T.regs 29 →
      MemFrame T.mem S2.mem [(s.sp.toNat - 80, s.sp.toNat - 32), (s.sp.toNat - 121, s.sp.toNat - 120)] →
      S2.mem.regions = T.mem.regions →
      S2.mem.readLE (s.sp.toNat - 56) 8 = (T.regs 0).toNat → S2.mem.readLE (s.sp.toNat - 48) 8 = (T.regs 1).toNat →
      S2.mem.readLE (s.sp.toNat - 40) 8 = (T.regs 2).toNat → S2.mem.readLE (s.sp.toNat - 80) 8 = (T.regs 3).toNat →
      S2.mem.readLE (s.sp.toNat - 72) 8 = (T.regs 4).toNat → S2.mem.readLE (s.sp.toNat - 64) 8 = (T.regs 5).toNat →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S2 Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T Q := by
  have mdw' : T.mem.readLE (s.sp.toNat - 32) 8 = 1807776 := mdw
  have e1 : (s.sp - 240#64 + 118#64).toNat = s.sp.toNat - 122 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have e2 : (s.sp - 240#64 + 224#64).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run [mfl, mrc, mdw'] until [1807776]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (simp only [Memory.regions_writeLE]; done) | (janus_simp; done) | skip
  all_goals first
    | (repeat (first
        | refine Janus.MemFrame.writeLE ?_ _ (r := (s.sp.toNat - 80, s.sp.toNat - 32)) (by simp) (by simp only; omega)
            (by simp only; omega)
        | refine Janus.MemFrame.writeLE ?_ _ (r := (s.sp.toNat - 121, s.sp.toNat - 120)) (by simp) (by simp only; omega)
            (by simp only; omega))
       exact MemFrame.refl _ _)
    | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]; done)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the closure call and the return: `deferwrap1`'s entry → `nat.div`'s return -/
theorem epiRD (impl : List Segment) {preD : State → Prop} {postD : State → State → Prop}
    (hD : Summary (LibDiv.program.link impl) dwD preD postD) {s : State} (Q : State → Prop)
    (hal : s.sp.toNat % 16 = 0) (hb' : 41504 ≤ s.sp.toNat) (ha : s.sp.toNat + 112 ≤ 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 dwD) (hsp : S.sp = s.sp - 240#64)
    (h30 : S.regs 30 = BitVec.ofNat 64 dwRD) (hpre : preD S) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hl4 : (s.regs 30).toNat % 4 = 0)
    (hK : ∀ s3 : State, postD S s3 → s3.mem.regions = S.mem.regions →
      s3.sp = S.sp ∧ s3.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true ∧
      s3.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat ∧
      ∀ s4 : State, s4.sp = s.sp →
        s4.regs 0 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 56) 8) →
        s4.regs 1 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 48) 8) →
        s4.regs 2 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 40) 8) →
        s4.regs 3 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 80) 8) →
        s4.regs 4 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 72) 8) →
        s4.regs 5 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 64) 8) →
        s4.regs 29 = BitVec.ofNat 64 (s3.mem.readLE (s.sp.toNat - 248) 8) →
        s4.regs 18 = s3.regs 18 → s4.regs 28 = s3.regs 28 → s4.mem = s3.mem → Q s4) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S Q := by
  refine ReachesRet.call_regions hD hpc hpre fun s3 hpc3 hpost hrg3 => ?_
  obtain ⟨e1, hacc3, h30v, K⟩ := hK s3 hpost hrg3
  rw [h30] at hpc3
  rw [hsp] at e1
  janus_run [h30v]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | rfl | (janus_simp; done) | skip
  all_goals (simp (disch := omega) only [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, Nat.reducePow,
    Nat.reduceMod]; first | rfl | (congr 2; omega) | skip)

end FvModexp.Arm64.NatDiv
