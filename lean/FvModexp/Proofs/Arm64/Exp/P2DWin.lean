import FvModexp.Proofs.Arm64.Exp.P2DWinR
import FvModexp.Proofs.Arm64.Exp.P2DOneR
import FvModexp.Proofs.Arm64.Exp.P2DPost
import FvModexp.Proofs.Arm64.Exp.P2W2EC

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): odd `x`, `logM ≥ 2` — the window call (agent infra)

`winCall`: from the window entry (`SP_c = SP - 112`) with a window summary `hW` (the `fullC` shape: pre
`P2W2.PreC … (stk - 112) …`, post `NHyp.CPostR … (stk - 112) 96 …`), through the epilogue (`epiW`) to the
return, post `PostD` (transport `cpre_sub` / `cpost_pre`). `natOne_sub`: the `natOne` facts one frame down.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the epilogue after a window call -/
theorem epiW (impl : List Segment) (Q : State → Prop) (sp r29 ret pc : Nat) (M : Memory)
    (he : Epi M sp r29 ret) (hpc0 : pc = w2R ∨ pc = w4R)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pc) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KF : ∀ s' : State, s'.sp = BitVec.ofNat 64 (sp + 112) → s'.regs 0 = S.regs 0 → s'.regs 1 = S.regs 1 →
      s'.regs 2 = S.regs 2 → s'.regs 18 = S.regs 18 → s'.regs 28 = S.regs 28 →
      s'.regs 29 = BitVec.ofNat 64 r29 → s'.mem = M → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, rfp, rlr, hr4, hr48⟩ := he
  generalize e0 : S.regs 0 = x0 at KF
  generalize e1 : S.regs 1 = x1 at KF
  generalize e2 : S.regs 2 = x2 at KF
  generalize e18 : S.regs 18 = x18 at KF
  generalize e28 : S.regs 28 = x28 at KF
  subst hmem
  rcases hpc0 with rfl | rfl
  · janus_run [rfp, rlr]
    refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals janus_simp
  · janus_run [rfp, rlr]
    refine KF _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals janus_simp

/-- the caller's FP/LR slots of the frame `sp` survive a callee at `sp` (frame `R.rt ++ winA … ++ [z] ++ stWs`) -/
theorem slot_keep {R : RtInv} {m m' : Memory} {sp stk' A' zp zc : Nat} {stw : List (Nat × Nat)}
    (h : MemFrame m m' (R.rt ++ [(sp - stk', sp - 8), (sp + 8, sp + A')] ++ [(zp, zp + 8 * zc)] ++ stw))
    {a : Nat} (ha : sp - 8 ≤ a ∧ a + 8 ≤ sp + 8) (hrt : Outside a 8 R.rt)
    (hz : 0 < zc → a + 8 ≤ zp ∨ zp + 8 * zc ≤ a) (hst : ∀ r ∈ stw, r.2 ≤ r.1 ∨ a + 8 ≤ r.1 ∨ r.2 ≤ a) :
    m'.readLE a 8 = m.readLE a 8 := by
  refine rd_frame h fun r hr => ?_
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((hr | rfl | rfl) | rfl) | hr
  · have := MemFrame.outside_mem hrt hr; omega
  · simp only; omega
  · simp only; omega
  · simp only; rcases Nat.eq_zero_or_pos zc with h0 | h0
    · left; omega
    · right; exact hz h0
  · exact hst r hr

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s S : State}

/-- the `natOne` facts at a callee entry one frame down -/
theorem natOne_sub (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {op : Nat}
    (hone : EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st))
    (hsa : EvenHyp.StkApart s.mem st op 8)
    (hF : MemFrame s.mem S.mem (ownW s stk A)) {L1 : List (Nat × Nat)} (hx : LiveExt R L L1)
    (hSsp : S.sp.toNat + 112 = s.sp.toNat) {stk' A' : Nat} (hk : stk' + 112 ≤ stk) (hA : A' ≤ 104)
    (ew : stW S.mem st = stW s.mem st) (el : stLen S.mem st = stLen s.mem st) (ec : stCap S.mem st = stCap s.mem st) :
    EvenHyp.NatOne R L1 S.mem op (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) ∧
      EvenHyp.StkApart S.mem st op 8 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hone
  have es : stWs S.mem st = stWs s.mem st := by unfold stWs stkWs; rw [ew, el, ec]
  have hwo : ∀ {a k : Nat}, Outside a k (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (ownW s stk A) := fun h => by
    simp only [win, ownW, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hww : ∀ {a k : Nat}, Outside a k (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) := fun h => by
    rw [es]; simp only [win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨⟨by omega, h.1.2⟩, h.2⟩
  have rd : ∀ k, k + 8 ≤ 24 → S.mem.readLE (EvenHyp.natOneA + k) 8 = s.mem.readLE (EvenHyp.natOneA + k) 8 :=
    fun k hk => hF.readLE _ _ ((hwo n7).of_sub (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, by rw [hF.readLE _ _ (hwo n11)]; exact n4, by rw [hF.accessible]; exact n5, n6, hww n7,
    by rw [hF.accessible]; exact n8, n9, hx.held n10, hww n11⟩, ?_⟩
  · have := rd 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact n1
  · rw [rd 8 (by omega)]; exact n2
  · rw [rd 16 (by omega)]; exact n3
  · intro h; obtain ⟨a1, a2⟩ := hsa h
    refine ⟨a1, fun hl => ?_⟩
    rw [el, ec] at hl; rw [ew, el, ec]; exact a2 hl

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the window call** (see the module doc) -/
theorem winCall {impl : List Segment} {e r : Nat} {cW : Nat → Nat}
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hXo : natVal s.mem xp xl % 2 = 1) (hlm2 : 2 ≤ lm) (hcW : cW (stLen s.mem st) ≤ cst)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (hW : Summary (LibW.program.link impl) e
      (fun s1 => Regs s1 zp zl zc st xp xl xc yp yl yc lm ∧
        P2W2.PreC R b L (stk - 112) (cW (stLen s1.mem st)) zp zl zc st xp xl yp yl lm s1 ∧
        (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48)
      (fun s1 s' => s'.sp = s1.sp ∧ s'.regs 18 = s1.regs 18 ∧ s'.regs 28 = s1.regs 28 ∧ s'.regs 29 = s1.regs 29 ∧
        NHyp.CPostR R b L (stk - 112) 96 zp zc st (natVal s1.mem xp xl ^ natVal s1.mem yp yl % 2 ^ lm)
          (cW (stLen s1.mem st)) s1 s'))
    (hr : r = w2R ∨ r = w4R)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 e) (esp : S1.sp = BitVec.ofNat 64 (s.sp.toNat - 112))
    (hR : Regs S1 zp zl zc st xp xl xc yp yl yc lm) (e18 : S1.regs 18 = s.regs 18)
    (e28 : S1.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat) (e30 : S1.regs 30 = BitVec.ofNat 64 r)
    (hm : S1.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S1
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  obtain ⟨hC, hX, hY, hlm1, hlm, hst0, op, hone, hsa⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hal, hle, h48, hacc⟩, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, ⟨-, -, hzW⟩, hins, hsok, hstw, -, harr,
    hcap0, hneed, -, -, -, -, -, -, hcb, hinv⟩ := hC'
  have h28 : S1.regs 28 = s.regs 28 := e28.trans (by simp)
  have hSsp : S1.sp.toNat + 112 = s.sp.toNat := by rw [esp, BitVec.toNat_ofNat]; omega
  generalize hSP : s.sp.toNat = SP at *
  have hsp1 : 8 ≤ SP - 112 := by omega
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hF0 : MemFrame s.mem S1.mem (ownW s stk A) := by
    rw [hm]; exact (w0_frame s.mem hsp1).mono fun a k ho => by
      simp only [ownW, hSP, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hF0' : MemFrame s.mem S1.mem (R.rt ++ ownW s stk A) := hF0.mono fun a k ho => by
    rw [outside_append] at ho; exact ho.2
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF0 : LiveFrame s.mem S1.mem L [] := LiveFrame.of_win hF0 hLs'
  have hrg : S1.mem.regions = s.mem.regions := by rw [hm]; simp only [W0, Memory.regions_writeLE]
  have hinv1 : R.inv b L (s.regs 28).toNat (view R.rt L S1.mem) := by
    refine RtInv.inv_frame hF0 (fun r hr => ?_) hinv
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact hwin.of_sub (by omega) (by omega)
  have hstO : Outside st 24 (ownW s stk A) := by
    simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF0' hLF0 hstO
  have hval : ∀ {p n : Nat}, (p, n) ∈ [(xp, xl), (yp, yl)] → natVal S1.mem p n = natVal s.mem p n := by
    intro p n hpn
    obtain ⟨⟨-, -, -, -, hw⟩, -⟩ := hins p n hpn
    exact hF0.readLE _ _ (by simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hw ⊢; omega)
  have hvx := hval (p := xp) (n := xl) (by simp)
  have hvy := hval (p := yp) (n := yl) (by simp)
  have hnone := natOne_sub hC hone hsa hF0 (LiveExt.refl R L) (by rw [hSP]; exact hSsp) (stk' := stk - 112) (A' := 96) (by omega)
    (by omega) ew el ec
  have hpre : P2W2.PreC R b L (stk - 112) (cW (stLen S1.mem st)) zp zl zc st xp xl yp yl lm S1 := by
    refine ⟨cpre_sub hC hF0' hLF0 hrg (LiveExt.refl R L) hinv1 (by rw [hSP]; exact hSsp) h28 (by omega) (by omega)
      (fun p n hpn => in_sub hC hpn hF0' hLF0 (LiveExt.refl R L) (by rw [hSP]; exact hSsp) (by omega) (by omega))
      (by omega) (by rw [el]; omega), by rw [hvx]; exact hXo, by rw [hvy]; exact hY, hlm2, hlm, hst0, op, hnone⟩
  have e30' : (S1.regs 30).toNat = r := by rw [e30, BitVec.toNat_ofNat]; rcases hr with rfl | rfl <;> decide
  refine ReachesRet.call_regions hW hpc ⟨hR, hpre, by rw [e30']; rcases hr with rfl | rfl <;> decide,
    by rw [e30']; rcases hr with rfl | rfl <;> decide⟩ fun s' hpc' hq hrg' => ?_
  obtain ⟨q1, q2, q3, q4, hcp⟩ := hq
  rw [hvx, hvy, el] at hcp
  have hcp' := hcp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hFc, -⟩ := hcp'
  have hS1 : S1.sp.toNat = SP - 112 := by omega
  simp only [winA, hS1, stWs, stkWs, ew, el, ec] at hFc
  have hst : ∀ {a : Nat}, SP - 120 ≤ a → a + 8 ≤ SP - 104 →
      ∀ q ∈ [(st, st + 24), (stW s.mem st + 8 * stLen s.mem st, stW s.mem st + 8 * stCap s.mem st)],
        q.2 ≤ q.1 ∨ a + 8 ≤ q.1 ∨ q.2 ≤ a := by
    intro a h1 h2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [win, hSP, outside_cons, outside_nil, and_true] at hstw
    rcases hq with rfl | rfl
    · simp only; omega
    · simp only
      rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
      · have := hcap0 h0; left; rw [this, h0]; have := hsok.2.2.2.2.2.1; omega
      · have := (harr h0).1
        simp only [win, hSP, outside_cons, outside_nil, and_true] at this
        right; omega
  have hz : ∀ {a : Nat}, SP - 120 ≤ a → a + 8 ≤ SP - 104 → 0 < zc → a + 8 ≤ zp ∨ zp + 8 * zc ≤ a := by
    intro a h1 h2 h0
    have := (hzW h0).1; simp only [win, hSP, outside_cons, outside_nil, and_true] at this; omega
  have hrt : ∀ {a : Nat}, SP - 120 ≤ a → a + 8 ≤ SP - 104 → Outside a 8 R.rt := fun h1 h2 =>
    hwin.of_sub (by omega) (by omega)
  have rfp : s'.mem.readLE (SP - 112 - 8) 8 = (s.regs 29).toNat := by
    rw [slot_keep hFc ⟨by omega, by omega⟩ (hrt (by omega) (by omega)) (hz (by omega) (by omega))
      (hst (by omega) (by omega)), hm]; exact w0_fp hsp1 (BitVec.isLt _)
  have rlr : s'.mem.readLE (SP - 112) 8 = (s.regs 30).toNat := by
    rw [slot_keep hFc ⟨by omega, by omega⟩ (hrt (by omega) (by omega)) (hz (by omega) (by omega))
      (hst (by omega) (by omega)), hm]; exact w0_lr hsp1 (BitVec.isLt _)
  have hacc' : s'.mem.accessible (SP - 112 - 8) 16 false = true := by
    rw [hFc.accessible, hm]; simp only [W0, Memory.accessible_writeLE]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
  rw [show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
  refine epiW impl _ (SP - 112) _ _ r s'.mem ⟨by omega, hsp1, by omega, hacc', rfp, rlr, hr4, hr48⟩ hr s'
    (hpc'.trans e30) (q1.trans esp) rfl fun s'' a1 a2 a3 a4 a5 a6 a7 a8 => ⟨?_, a5.trans (q2.trans e18),
      a6.trans (q3.trans h28), a7.trans (by simp), ?_⟩
  · rw [a1]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hSP]; omega
  · exact cpost_pre hC hF0' hLF0 (LiveExt.refl R L) (by rw [hSP]; exact hSsp) h28 (stk' := stk - 112) (A' := 96)
      (by omega) (by omega) (by omega) hcp a8 a2 a3 a4

end

end FvModexp.Arm64.P2D
