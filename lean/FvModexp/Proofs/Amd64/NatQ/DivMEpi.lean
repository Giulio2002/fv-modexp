import FvModexp.Proofs.Amd64.NatQ.DivMJoin

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`: the epilogue after `divLarge` with the deferred `stk.free()` (natdiv.go:543-544) (top s42)

Twin of Arm64/NatQ/DivMEpi.lean (`sp` = the entry `RSP`; `RSP = sp - 232` in the body).
`epiCM`: from `divLarge`'s return `retL` (`fn + 0x41d`): the result stores (`q` = `RAX, RBX, RCX` → `sp - 56 … - 40`,
`r` = `RDI, RSI, R8` → `sp - 80 … - 64`), the defer bit test (`[sp - 122]` = 1: `JE` not taken), `MOVB $0, [sp - 121]`,
`RDX := [sp - 16]` (= `sp - 32`, the closure record), `RAX := [RDX]` (= `nat.div.deferwrap1`), `CALL AX` — stops at the
closure entry (return address `dwRM = fn + 0x569` pushed at `sp - 240`).
`epiRM`: the closure call (any `Summary` of `deferwrap1` on `LibDiv`), the result reloads, `ADDQ $0xe0, SP; POPQ BP;
RET`. Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

/-- the return point of the closure call (`fn + 0x569`) -/
abbrev dwRM : Nat := 0x5ee389

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- result stores, defer-bit test, closure call: `retL` → `deferwrap1`'s entry -/
theorem epiCM (impl : List Amd64.Segment) {s : State} (ret0 : BitVec 64) (Q : State → Prop)
    (hb' : 41512 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 retL) (hsp : T.regs 4 = s.regs 4 - 232#64)
    (hacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true)
    (mfl : T.mem.readLE ((s.regs 4).toNat - 122) 1 = 1)
    (mrc : T.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32)
    (mdw : T.mem.readLE ((s.regs 4).toNat - 32) 8 = dwM)
    (k : ∀ S2 : State, S2.rip = BitVec.ofNat 64 dwM → S2.regs 4 = s.regs 4 - 240#64 →
      S2.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 32) → S2.regs 5 = T.regs 5 → S2.regs 14 = T.regs 14 →
      S2.xmm = T.xmm → S2.fsBase = T.fsBase → S2.df = T.df →
      MemFrame T.mem S2.mem [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
        ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120)] →
      S2.mem.regions = T.mem.regions → S2.mem.readLE ((s.regs 4).toNat - 240) 8 = dwRM →
      S2.mem.readLE ((s.regs 4).toNat - 56) 8 = (T.regs 0).toNat →
      S2.mem.readLE ((s.regs 4).toNat - 48) 8 = (T.regs 3).toNat →
      S2.mem.readLE ((s.regs 4).toNat - 40) 8 = (T.regs 1).toNat →
      S2.mem.readLE ((s.regs 4).toNat - 80) 8 = (T.regs 7).toNat →
      S2.mem.readLE ((s.regs 4).toNat - 72) 8 = (T.regs 6).toNat →
      S2.mem.readLE ((s.regs 4).toNat - 64) 8 = (T.regs 8).toNat →
      ReachesRet (LibDiv.program.link impl) ret0 S2 Q) :
    ReachesRet (LibDiv.program.link impl) ret0 T Q := by
  have mdw' : T.mem.readLE ((s.regs 4).toNat - 32) 8 = 6218880 := mdw
  janus64_run [mfl, mrc, mdw'] until [dwM]
  refine k _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus_frame) ?reg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case reg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals try rfl
  all_goals
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  all_goals first
    | exact Nat.mod_eq_of_lt (BitVec.isLt _)
    | (janus64_simp; omega)
    | (simp only [BitVec.toNat_ofNat, BitVec.toNat_sub]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the closure call and the return: `deferwrap1`'s entry → `nat.div`'s return -/
theorem epiRM (impl : List Amd64.Segment) {preD : State → Prop} {postD : State → State → Prop}
    (hD : Summary (LibDiv.program.link impl) dwM preD postD) {s : State} (Q : State → Prop)
    (hb' : 41512 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 dwM) (hsp : S.regs 4 = s.regs 4 - 240#64)
    (hra : S.mem.readLE ((s.regs 4).toNat - 240) 8 = dwRM) (hpre : preD S)
    (hr47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hK : ∀ s3 : State, postD S s3 → s3.mem.regions = S.mem.regions →
      s3.regs 4 = S.regs 4 + 8#64 ∧ s3.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true ∧
      s3.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
      ∀ s4 : State, s4.regs 4 = s.regs 4 + 8#64 →
        s4.regs 0 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 56) 8) →
        s4.regs 3 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 48) 8) →
        s4.regs 1 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 40) 8) →
        s4.regs 7 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 80) 8) →
        s4.regs 6 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 72) 8) →
        s4.regs 8 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 64) 8) →
        s4.regs 5 = BitVec.ofNat 64 (s3.mem.readLE ((s.regs 4).toNat - 8) 8) →
        s4.regs 14 = s3.regs 14 → s4.xmm = s3.xmm → s4.fsBase = s3.fsBase → s4.df = s3.df →
        s4.mem = s3.mem → Q s4) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q := by
  refine ReachesRet.call_regions hD hpc hpre fun s3 hpc3 hpost hrg3 => ?_
  obtain ⟨e4, hacc3, hrv, K⟩ := hK s3 hpost hrg3
  have hpc3' : s3.rip = BitVec.ofNat 64 dwRM := by
    rw [hpc3, retAddrOf, hsp, show (s.regs 4 - 240#64).toNat = (s.regs 4).toNat - 240 by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega, hra]
  have h4 : s3.regs 4 = s.regs 4 - 232#64 := by rw [e4, hsp]; bv_omega
  clear hpc3 e4 hpost hpre
  show ReachesRet _ (BitVec.ofNat 64 (s.mem.readLE (s.regs 4).toNat 8)) _ _
  janus64_run [hrv]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
  all_goals first | rfl | (janus64_simp; done) | skip
  all_goals (simp (disch := omega) only [setRegF_apply, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add,
    Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]; first | rfl | (congr 2; omega) | bv_omega | skip)

end FvModexp.Amd64.Q.NatDiv
