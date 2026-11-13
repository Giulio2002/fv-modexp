import FvModexp.Proofs.Amd64.NatQ.DrsAt
import FvModexp.Proofs.Amd64.NatQ.DrsFin

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): `len u == 0` — `clear(z)` and return (natdiv.go:756-759)

From the dispatch: `TESTQ R8, R8; JE 0x5efa24` (taken), `TESTQ BX, BX; JE 0x5efa32` (`len z == 0`: nothing to clear),
otherwise `SHLQ $3, BX; CALL runtime.memclrNoHeapPointers` (`AX = z.ptr`, `BX = 8·len z`), then the epilogue at
`0x5efa32`. Twin of Arm64/NatQ/DrsEntry.lean `pathA`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `runtime.memclrNoHeapPointers(dst, n)` called from `divRecursiveStep`'s frame (`S` = the callee entry, `RSP = r - 400`) -/
theorem mcz_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s : State} {W : Nat} (hce : CallEnv R L s W 96)
    (hW : 4600 ≤ W) (hsv : Serves R) (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (S : State)
    (hF : MemFrame s.mem S.mem (fw s)) (hsp : (S.regs 4).toNat + 400 = (s.regs 4).toNat)
    (h14 : S.regs 14 = s.regs 14) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) (hx15 : S.xmm 15 = 0#128)
    (hdf : S.df = false) {dst n : Nat} (h0 : (S.regs 0).toNat = dst) (h3 : (S.regs 3).toNat = n)
    (hn : n ≤ 2 ^ 20) (hd48 : dst + n ≤ 2 ^ 48) (hdacc : s.mem.accessible dst n true = true) (hdh : Held R L dst n)
    (hdw : Outside dst n (win s W 96)) :
    MemPre64 4096 2 S ∧
      LiveMemAt64 R (cA "runtime.memclrNoHeapPointers") [(S.regs 0).toNat, (S.regs 3).toNat] L b S
        (liveWin64 S 4096 2) ∧
      LiveDest64 R L S 4096 2 (S.regs 0).toNat (S.regs 3).toNat := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  simp only [win, outside_cons, outside_nil, and_true] at hdw
  unfold Apart at hga
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hF.readLE _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)
  have hrt : ∀ r ∈ fw s, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L := by
    intro r hr
    simp only [fw, win, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  have hdh' : InRanges dst n L ∨ Outside dst n R.rt := hdh
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨by omega, by omega, by omega, ?_, hx15, hdf, hra⟩, ?_⟩,
    ⟨?_, by rw [h14]; exact RtInv.inv_frame' hF hrt hinv, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stackguard0Offset, regG, h14]; omega
  · simp only [stackguard0Offset, regG, h14]; rw [hF.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP, h14]; rw [hgS]; omega
  · rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, h14, outside_cons, outside_nil, and_true]; omega
  · rw [h0, h3]; exact hsv.2.2.1 _ _ (by omega)
  · intro r hr
    have := hLs r hr
    simp only [win, liveWin64, calleeStack64, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro r hr
    simp only [liveWin64, calleeStack64, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  · rw [h0, h3]; exact hd48
  · rw [h0, h3, hF.accessible]; exact hdacc
  · simp only [calleeStack64, outside_cons, outside_nil, and_true]; rw [h0, h3]; omega
  · rw [h0, h3]; exact hdh'
  · simp only [outside_cons, outside_nil, and_true]; rw [h0, h3]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`len u == 0`**: `clear(z)` (when `len z > 0`) and return at `0x5efa32` -/
theorem pathA (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp a.vl a.vc s) (hW : 4600 ≤ a.W) (P : State)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat 0 a.uc.toNat a.vp a.vl a.vc a.d.toNat)
    (hU : natVal s.mem a.up.toNat 0 = natVal s.mem a.up.toNat a.ul.toNat) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp a.vl s s') := by
  have hU0 : natVal s.mem a.up.toNat a.ul.toNat = 0 := by rw [← hU]; rfl
  have hq0 := hpre.q0
  have hqlc := hpre.qlc
  have hqc := hpre.qc40
  obtain ⟨hqa, hq48, hqh, hqo, -⟩ := hpre.qa
  have hce := hpre.ce
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  obtain ⟨hra, hx15, hdf, -⟩ := hE
  have hF := hA.fr
  have hpc := hA.pc
  have h8 := hA.r8
  have h3 := hA.r3
  have h0 := hA.r0
  have hx0 := hA.x15
  have hacc8 : P.mem.accessible ((s.regs 4).toNat - 8) 16 false = true := by
    rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hsp0 := hF.sp
  rcases Nat.eq_zero_or_pos a.ql.toNat with hz | hz
  · -- `len z == 0`: nothing to clear
    rw [hz] at h3
    janus64_run until [epZ]
    refine epi impl s _ epZ (Or.inr (Or.inr rfl)) rfl ?sp ?r14 ?fs ?df ?ra ?bp ?x hdf hra (by omega) (by omega) ?acc _
      fun s' ⟨e1, e2, e3, e4⟩ => ⟨e1, post_frame hpre (by omega) (by rw [e4]; exact hF.fr) e2 e3 ?q ?u⟩
    case sp => first | exact hF.sp | (janus64_simp; exact hF.sp)
    case r14 => first | exact hF.r14 | (janus64_simp; exact hF.r14)
    case fs => first | exact hF.fs | (janus64_simp; exact hF.fs)
    case df => first | exact hF.df | (janus64_simp; exact hF.df)
    case ra => first | exact hF.ra | (janus64_simp; exact hF.ra)
    case bp => first | exact hF.bp | (janus64_simp; exact hF.bp)
    case x => first | (rw [hx0, hx15]) | (janus64_simp; rw [hx0, hx15])
    case acc => first | exact hacc8 | (janus64_simp; exact hacc8)
    case q => rw [hq0, hU0]; simp
    case u => rw [hU0]; simp
  · have hne : (BitVec.ofNat 64 a.ql.toNat = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 392 := by
      rw [hsp0, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    have hpush : P.mem.accessible ((P.regs 4).toNat - 8) 8 true = true := by
      rw [hspP, hF.fr.accessible]
      exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    janus64_run [hne, hpush] until [cA "runtime.memclrNoHeapPointers"]
    have e400 : (s.regs 4 - 400#64).toNat = (s.regs 4).toNat - 400 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    have hql3 : (a.ql <<< 3).toNat = 8 * a.ql.toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
    have hfw0 : MemFrame P.mem (P.mem.writeLE ((s.regs 4).toNat - 400) 8 6224434) (fw s) := by
      unfold fw win; janus_frame
    refine ReachesRet.call (hmc a.L a.b) rfl (mcz_pre hce (by omega) hpre.sv hpre.inv _ (mf_trans hF.fr hfw0)
      (by simp only [Janus.Amd64.Tactic.setRegF_apply, ite_true]; rw [e400]; omega)
      (by simp only [Janus.Amd64.Tactic.setRegF_apply]; exact hF.r14)
      (by simp only [Janus.Amd64.Tactic.setRegF_apply, ite_true, e400]; rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide)
      (by exact hx0) (by exact hF.df) (dst := a.qp.toNat) (n := 8 * a.ql.toNat)
      (by simp only [Janus.Amd64.Tactic.setRegF_apply]; rw [h0]; simp)
      (by simp only [Janus.Amd64.Tactic.setRegF_apply]; exact hql3) (by have := hpre.v9; omega) hq48 hqa hqh hqo) ?_
    intro S3 hpc3 ⟨junk, f3, x3, yh3, m3, zh3, kr3, hs3, hMF3, hLF3, hinv3, hz3⟩
    subst hs3
    have e392 : s.regs 4 - 400#64 + 8#64 = s.regs 4 - 392#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, e400, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]; omega
    have h0q : (P.regs 0).toNat = a.qp.toNat := by rw [h0]; simp
    simp only [calleeStack64, Janus.Amd64.Tactic.setRegF_apply, ite_true, e400, h0q, hql3, Nat.reduceEqDiff,
      ↓reduceIte] at hMF3 hLF3 hinv3 hz3 hpc3
    have hout := hce.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at hqo
    have hrd3 : ∀ a' n, (s.regs 4).toNat - 8 ≤ a' → a' + n ≤ (s.regs 4).toNat + 8 →
        m3.readLE a' n = P.mem.readLE a' n := fun a' n h1 h2 => by
      rw [hMF3.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have hacc3 : ∀ a' n w, m3.accessible a' n w = P.mem.accessible a' n w := fun a' n w => by
      rw [hMF3.accessible, Janus.Arm64.Memory.accessible_writeLE]
    refine epi impl s _ epZ (Or.inr (Or.inr rfl)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hdf hra (by omega) (by omega) ?_ _
      fun s' ⟨e1, e2, e3, e4⟩ => ⟨e1, post_clr hpre (by omega) (mf_trans hF.fr hfw0) (by rw [e4]; exact hMF3)
        (by rw [e4]; exact hLF3) ?_ e2 e3 (by rw [e4]; simp only [retState64]; rw [← hF.r14]; exact hinv3) ?_ (by rw [hU0]; simp)⟩
    · simp only [retState64, retAddrOf, Janus.Amd64.Tactic.setRegF_apply, ite_true, e400,
        Janus.Arm64.Memory.readLE_writeLE_self]
    · simp only [retState64, callRegs64_apply, Janus.Amd64.Tactic.setRegF_apply, ite_true]; exact e392
    · simp only [retState64, callRegs64_apply, Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte,
        or_true]; exact hF.r14
    · exact hF.fs
    · exact hF.df
    · simp only [retState64]; rw [hrd3 _ _ (by omega) (by omega)]; exact hF.ra
    · simp only [retState64]; rw [hrd3 _ _ (by omega) (by omega)]; exact hF.bp
    · simp only [retState64, ite_true]; rw [hx0, hx15]
    · simp only [retState64]; rw [hacc3]; exact hacc8
    · intro a' n ho; simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · have hz' : natVal s'.mem a.qp.toNat a.ql.toNat = 0 := by rw [e4]; exact FvModexp.Expmc.readLE_zeroed hz3
      rw [hz', hU0]; simp

end FvModexp.Amd64.Q.DivRec
