import FvModexp.Proofs.Amd64.Nat.DivOneF

set_option autoImplicit false

/-!
# `nat.div` (amd64), `len v = 1`: `r = z2.setWord(r2)`, return (natdiv.go:528-529, nat.go:72-77) — `r2 = 0`

From `AtW` (`fn + 0xb6`): `q` stored at `SP - 56 … -40`; `RDI = r2 = 0` → `r = z2[:0]` (`oneA`); `r` stored at
`SP - 80 … -64`, results reloaded (`q` = `RAX, RBX, RCX`, `r` = `RDI, RSI, R8`), `ADDQ $0xe0, SP; POPQ BP; RET`.
Port of `Arm64/Nat/DivOneT.lean` (`oneA`; `oneB`/`oneC` in `DivOneTB`/`DivOneTC`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `r2 = 0`: `r = z2[:0]` -/
theorem oneA (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v 1 vc s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L zp zc z2 z2c u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 = 0) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) T (RQ R b dc L zp zc st z2 z2c u ul v 1 s) := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hz2 := hp.z2o
  have hext := hW.ext
  have hB : Box (Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v 1 vc s ∧
      AtW R b L zp zc z2 z2c u ul v 1 s q ql qc L' b' T) := ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h5 := hW.r5; have h14 := hW.r14; have hfs := hW.fs
  have hx15 := hW.x15; have hdf := hW.df
  have hr0' := hW.r0; have hr3 := hW.r3; have hr1 := hW.r1
  have h7 : T.regs 7 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hW.r7, hr0]; rfl)
  have hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hW.mf.accessible]; exact hw
  have m1 := hW.ra; have m2 := hW.bp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  have hacc := hW.mf.accessible
  clear hpre hW hp
  janus64_run [m1, m2, m5, m7, h7]
  obtain ⟨hpre, hW⟩ := hB.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFin (r := z2) (rl := 0) (rc := z2c) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF
    (LiveExt.refl R L') (Nat.sub_le _ _) ?hI ?hR⟩
  case hM => exact (winFrame hce hext (by janus_frame) (lo := (s.regs 4).toNat - 80)
    (hi := (s.regs 4).toNat - 32) (by omega) (by omega) z2 z2c).1
  case hLF => exact (winFrame hce hext (by janus_frame) (lo := (s.regs 4).toNat - 80)
    (hi := (s.regs 4).toNat - 32) (by omega) (by omega) z2 z2c).2
  case hI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 80, (s.regs 4).toNat - 32)]) (by janus_frame)
      (fun r hr => ?_) hinvT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hR =>
    refine ⟨by simp [natVal, hr0], Or.inl rfl, Nat.zero_le _, hz2.1, natLive_ext hz2.2.1 ?_ hext, Or.inl ⟨rfl, rfl⟩⟩
    intro a n w; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hacc]
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hx15.trans hx0.symm
    | exact hfs
    | (rw [hdf0]; rfl)
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)

end FvModexp.Amd64.NatDiv
