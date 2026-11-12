import FvModexp.Proofs.Arm64.Exp.P2DLshR
import FvModexp.Proofs.Arm64.Exp.P2DRet
import FvModexp.Proofs.Arm64.Exp.CallWW

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `return z.lsh(z, lo)` (nat.go:955; agent infra)

`lshPath`: from `recR` (the recursive call's exit facts at the entry level, result `(p2, l2, c2)` of value `v1`,
`0 < v1 < 2^lm'`) through `runL`, asm's `Lsh.Hyp2` (`z = x = (p2, l2, c2)`, `sh = lo`; window
`[sp - stkL, sp + aboveL)` inside ours) and `epiL` to the function's exit: `PostD` with value `v1 · 2^lo` and cost
`cst1 + makeCost (lm / 64 + 2)` (`lsh` needs `l2 + lo/64 + 1 ≤ lm/64 + 2` words).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

theorem mk_mono {a k : Nat} (h : a ≤ k) (hk : 2 ≤ k) : makeCost a ≤ makeCost k := by
  unfold makeCost makeCap allocCost; split <;> split <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the entry ranges a callee may have written are accessible at entry and apart from the guard word -/
theorem ws_facts (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) :
    (∀ r ∈ winA s stk A ++ ([(zp, zp + 8 * zc)] ++ stWs s.mem st), r.1 < r.2 →
      s.mem.accessible r.1 (r.2 - r.1) true = true) ∧
    (∀ r ∈ winA s stk A ++ ([(zp, zp + 8 * zc)] ++ stWs s.mem st),
      r.2 ≤ r.1 ∨ (s.regs 28).toNat + 16 + 8 ≤ r.1 ∨ r.2 ≤ (s.regs 28).toNat + 16) := by
  obtain ⟨⟨-, ⟨hal, hle, h48, hacc⟩, -, -, hgw, -, -, -⟩, -, -, -, -, -, ⟨-, hzL, hzW⟩, -, hsok, -, hstg, harr,
    -, -, -, -, -, -, -, -, -, -⟩ := hP
  have hlc := hsok.2.2.2.2.2.1
  unfold Apart at hgw hstg
  refine ⟨fun r hr h12 => ?_, fun r hr => ?_⟩
  all_goals
    simp only [winA, stWs, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only at h12 ⊢
    · exact Memory.accessible_mono _ hacc (by omega) (by omega)
    · exact Memory.accessible_mono _ hacc (by omega) (by omega)
    · rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact (hzL (by omega)).2.2.1
    · rw [show st + 24 - st = 24 by omega]; exact hsok.2.2.1
    · have h0 : 0 < stCap s.mem st := by omega
      exact Memory.accessible_mono _ (hsok.2.2.2.2.1 h0).2.2.1 (by omega) (by omega)
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only
    · omega
    · omega
    · rcases Nat.eq_zero_or_pos zc with h0 | h0
      · left; omega
      · have := (hzW h0).2; unfold Apart at this; omega
    · omega
    · rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
      · left; omega
      · have := (harr h0).2; unfold Apart at this; omega

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl yp yl lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `lsh` call and the exit** (see the module doc) -/
theorem lshPath {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains NHyp.fnP2 = false)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL + 112 ≤ stk) (haL : aboveL ≤ 88)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    {lo lm' v1 cst1 w : Nat} (hlo0 : 0 < lo) (hlm' : lm' + lo ≤ lm) (hv0 : 0 < v1) (hvb : v1 < 2 ^ lm')
    (hw : v1 * 2 ^ lo = w) (hbud : cst1 + makeCost (lm / 64 + 2) ≤ cst)
    (S3 : State) (h3pc : S3.pc = BitVec.ofNat 64 recR) (h3sp : S3.sp = BitVec.ofNat 64 (s.sp.toNat - 112))
    (h318 : S3.regs 18 = s.regs 18) (h328 : S3.regs 28 = s.regs 28) (h3rg : S3.mem.regions = s.mem.regions)
    (f1 : S3.mem.readLE (s.sp.toNat - 16) 8 = lo) (f2 : S3.mem.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat)
    (f3 : S3.mem.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat)
    (hcp : NHyp.CPostR R b L stk A zp zc st v1 cst1 s S3) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S3 (PostD R b L stk A cst zp zc st w s) := by
  obtain ⟨hC, -, -, -, hlm, -, -, -, -⟩ := hP
  have hC' := hC
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, -, hwrt, hgw, hgrt, -, -⟩, hsv, -, -, -, -, ⟨-, hzL, hzW⟩, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hcb, -⟩ := hC'
  obtain ⟨hws, hgws⟩ := ws_facts hC
  obtain ⟨p2, l2, c2, q0, q1, q2, L2, b2, hres, ⟨hx2, hb2, hinv2⟩, hsb, hF1, hLF1, hrs⟩ := hcp
  have hres0 := hres
  obtain ⟨hv, hn, hlc, hc40, hlive, hloc⟩ := hres0
  have hF1a : MemFrame s.mem S3.mem (R.rt ++ (winA s stk A ++ ([(zp, zp + 8 * zc)] ++ stWs s.mem st))) := by
    simpa only [List.append_assoc] using hF1
  have hcen := cenv_ofW hC hF1a hws hgws h3rg hx2 (by omega)
  generalize hSP : s.sp.toNat = SP at *
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  -- the recursive result
  have hl2 : l2 ≤ (lm' + 63) / 64 := lenLe hn (by
    rw [hv]; exact Nat.lt_of_lt_of_le hvb (Nat.pow_le_pow_right (by decide) (by omega)))
  have hl20 : 0 < l2 := by
    rcases Nat.eq_zero_or_pos l2 with h | h
    · subst h; simp [natVal] at hv; omega
    · exact h
  have hnd : l2 + lo / 64 + 1 ≤ lm / 64 + 2 := by omega
  have hmk : makeCost (l2 + lo / 64 + 1) ≤ makeCost (lm / 64 + 2) := mk_mono hnd (by omega)
  have hc0 : 0 < c2 := by omega
  obtain ⟨hp8, hpH, hpacc, hp48⟩ := hlive hc0
  have hpW : Apart p2 (8 * c2) (SP - stk) (stk + A) ∧ Apart p2 (8 * c2) ((s.regs 28).toNat + 16) 8 := by
    rcases hloc with ⟨e1, e2⟩ | ⟨-, hin, -⟩
    · rw [e2] at hc0; rw [e1, e2]
      obtain ⟨h1, h2⟩ := hzW hc0
      simp only [win, hSP, outside_cons, outside_nil, and_true] at h1
      exact ⟨by unfold Apart; omega, h2⟩
    · have a1 := hin.apart hwin
      have a2 := hin.apart hgrt
      unfold Apart at a1 a2 ⊢; omega
  -- `runL` to the `lsh` entry
  have hacc96 : S3.mem.accessible (SP - 112 + 96) 8 false = true := by
    rw [hF1.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
  refine runL (s.regs 30) _ (SP - 112) lo S3.mem (by omega) (by omega) hacc96
    (by rw [show SP - 112 + 96 = SP - 16 by omega]; exact f1) S3 h3pc h3sp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r30 r18 r28 r29
  have hS'sp : S'.sp.toNat = SP - 112 := by rw [fsp, h3sp, BitVec.toNat_ofNat]; omega
  have e28 : S'.regs 28 = s.regs 28 := r28.trans h328
  have hS := CallWW.hypSum hap hns (hlh b2 L2 (BitVec.ofNat 64 p2) (BitVec.ofNat 64 l2) (BitVec.ofNat 64 c2)
    (BitVec.ofNat 64 p2) (BitVec.ofNat 64 l2) (BitVec.ofNat 64 c2) (BitVec.ofNat 64 lo))
  have tp := tN (show p2 < 2 ^ 64 by omega)
  have tl := tN (show l2 < 2 ^ 64 by omega)
  have tc := tN (show c2 < 2 ^ 64 by omega)
  have tlo := tN (show lo < 2 ^ 64 by omega)
  simp only [tp, tl, tc, tlo] at hS
  have hwo : Outside p2 (8 * c2) (win S' stkL aboveL) := by
    have := hpW.1; simp only [win, hS'sp, outside_cons, outside_nil, and_true]; unfold Apart at this; omega
  have hg' : (S'.regs 28).toNat = (s.regs 28).toNat := by rw [e28]
  refine ReachesRet.call_regions hS (by rw [f0, ← lsh_a]) ⟨?_, ?_, ?_⟩
    fun s'' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg' => ?_
  · rw [r30, tN (by simp only [lshR]; omega)]; exact ra_p2 hap hnf 126 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0.trans q0, r1.trans q1, r2.trans q2, r3.trans q0, r4.trans q1, r5.trans q2, r6, trivial⟩
  · refine ⟨⟨CallW.callEnv_of hcen (fsp.trans h3sp) (by rw [e28]; simp) fm (by omega) haL, hsv, hlc,
      ⟨hc40, by rw [fm]; exact hlive, fun _ => ⟨hwo, by rw [hg']; exact hpW.2⟩⟩,
      ⟨by omega, by rw [fm]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hpacc (Nat.le_refl _)
        (by omega)), by omega, hpH.sub (Nat.le_refl _) (by omega), hwo.of_sub (Nat.le_refl _) (by omega)⟩,
      by omega, Or.inl rfl, by omega, by rw [hg', fm]; exact hinv2⟩, hlo0, hl20⟩
  · obtain ⟨p', l', c', g0, g1', g2', L3, b3, hres', hcap', ⟨hx3, hb3, hinv3⟩, hF2, hLF2⟩ := hq
    rw [fm, hv, hw] at hres'
    rw [fm] at hF2 hLF2
    rw [hg'] at hinv3
    simp only [winA, hS'sp] at hF2
    -- the saved FP/LR survive `lsh`
    have hrd : ∀ a, SP - 120 ≤ a → a + 8 ≤ SP - 104 → s''.mem.readLE a 8 = S3.mem.readLE a 8 := fun a h1 h2 =>
      rd_frame hF2 fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (hr | rfl | rfl) | rfl
        · have := MemFrame.outside_mem (hwin.of_sub (a := a) (n := 8) (by omega) (by omega)) hr; omega
        · simp only; omega
        · simp only; omega
        · have := hpW.1; unfold Apart at this; simp only; omega
    have rfp : s''.mem.readLE (SP - 112 - 8) 8 = (s.regs 29).toNat := by
      rw [hrd _ (by omega) (by omega), show SP - 112 - 8 = SP - 120 by omega]; exact f2
    have rlr : s''.mem.readLE (SP - 112) 8 = (s.regs 30).toNat := by
      rw [hrd _ (by omega) (by omega)]; exact f3
    have hacc' : s''.mem.accessible (SP - 112 - 8) 16 false = true := by
      rw [hF2.accessible, hF1.accessible]
      exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
    rw [show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
    refine epiL impl _ (SP - 112) _ _ s''.mem ⟨by omega, by omega, by omega, hacc', rfp, rlr, hr4, hr48⟩ s''
      (hr.trans r30) (e1.trans (fsp.trans h3sp)) rfl fun s' a1 a2 a3 a4 a5 a6 a7 a8 =>
        ⟨?_, a5.trans (e4.trans (r18.trans h318)), a6.trans (e2.trans e28), a7.trans (by simp), ?_⟩
    · rw [a1]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hSP]; omega
    · have hcw : ∀ a k, Outside a k (winA s stk A) →
          Outside a k [(SP - 112 - stkL, SP - 112 - 8), (SP - 112 + 8, SP - 112 + aboveL)] := fun a k h => by
        simp only [winA, hSP, outside_cons, outside_nil, and_true] at h ⊢; omega
      exact cpostR_lsh hC ⟨hv, hn, hlc, hc40, hlive, hloc⟩ hx2 hb2 ⟨hsb.1, hsb.2⟩ hF1 hLF1 hrs hcw hres' hcap'
        (by omega) hx3 hb3 hinv3 hF2 hLF2 (Nat.le_trans (Nat.add_le_add_left hmk _) hbud) a8
        (a2.trans g0) (a3.trans g1') (a4.trans g2')

end

end FvModexp.Arm64.P2D
