import FvModexp.Proofs.Amd64.NatQ.DivLessRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLess.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64), `u < v` (`len v ≥ 2`), `len u ≤ cap z2`: `q = z[:0]`, `r = z2[:len u]` → `AtS`
(natdiv.go:532-534, nat.go:58). Port of `Arm64/Nat/DivLess.lean`'s `lessR`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `len u ≤ cap z2`: `r = z2[:len u]` -/
theorem lessR (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b H dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (hr0 : S.regs 0 = 18446744073709551615#64)
    (hz : ul ≤ z2c) (Q : State → Prop)
    (k : ∀ S', AtS R b L zp zc z2 z2c u ul s z2 z2c L b S' →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hinv0 := hp.inv
  have hul := hp.ul9
  have hz40 := hp.z2o.1
  obtain ⟨hinv1, hmf1, hlf1⟩ := winOnly hce hinv0 hS.mf
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hS.mf.accessible]; exact hw
  have m0 := hS.ra; have m1 := hS.bp; have m3 := hS.s1; have m4 := hS.s3; have m5 := hS.s5; have m6 := hS.s7
  have m7 := hS.s8; have m8 := hS.s9
  have hreg := hS.reg
  have hzp : zp < 2 ^ 64 := by rw [← hS.s1]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.s3]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  clear hpre hp hS hce hinv0
  janus64_run [hr0, m0, m1, m3, m4, m5, m6, m7, m8, BitVec.msb_eq_decide] until [joinS]
  refine k _
    { pc := rfl
      sp := ?_
      r5 := ?_
      r14 := ?_
      fs := ?_
      x15 := ?_
      df := ?_
      r0 := ?_
      r1 := ?_
      r3 := ?_
      r2 := ?_
      arr := Or.inl ⟨rfl, rfl, hz⟩
      ext := LiveExt.refl R L
      bud := Nat.sub_le _ _
      inv := RtInv.inv_frame' (ws := [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)]) (by janus_frame)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          left; exact hout.of_sub (by simp only; omega) (by simp only; omega)) hinv1
      mf := hmf1.trans (by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)])
        fun a n h => ⟨h, by simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
      lf := ⟨fun a n hin ho => by
        rw [(by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 56, (s.regs 4).toNat - 32)]).readLE a n ?_]
        · exact hlf1.readLE a n hin ho
        · obtain ⟨r, hr, i1, i2⟩ := hin
          have := hLs r hr
          simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega⟩
      reg := ?_
      ra := ?_
      bp := ?_
      q0 := ?_
      q1 := ?_
      q2 := ?_
      s8 := ?_ }
  all_goals try (janus64_simp; done)
  all_goals first | exact hx15 | exact hdf | exact hfs | (janus64_simp; omega)

end FvModexp.Amd64.Q.NatDiv
