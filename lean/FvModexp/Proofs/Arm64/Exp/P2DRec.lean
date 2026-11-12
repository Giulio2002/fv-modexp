import FvModexp.Proofs.Arm64.Exp.P2DRsh

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `z = z.expNNPowerOfTwo(stk, xOdd, y, logM - lo)` (nat.go:954; agent infra)

`runRec`: `rshR` → the recursive call's entry `fnE` (`R4..R6` = `rsh`'s result, `R10 = logM - lo`, `R30 = recR`).
`recCall`: from `rshR` (with `rsh`'s `RshPost`) through the odd-base summary (`hO`, = `sumO` with window
`[sp - (stk - 112), sp + 96)`) to `recR`, handing on the callee's exit facts transported to the entry (`cpost_pre`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

abbrev recR : Nat := 1792772

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `rshR` → `fnE` -/
theorem runRec {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp zp zl zc st yp yl yc lm lo : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 208 ≤ 2 ^ 48) (hacc : M.accessible (sp + 96) 112 false = true)
    (h200 : M.readLE (sp + 200) 8 = lm) (h96 : M.readLE (sp + 96) 8 = lo) (h144 : M.readLE (sp + 144) 8 = st)
    (h176 : M.readLE (sp + 176) 8 = yp) (h184 : M.readLE (sp + 184) 8 = yl) (h192 : M.readLE (sp + 192) 8 = yc)
    (h120 : M.readLE (sp + 120) 8 = zp) (h128 : M.readLE (sp + 128) 8 = zl) (h136 : M.readLE (sp + 136) 8 = zc)
    (hlo : lo ≤ lm)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 rshR) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 fnE → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 zl → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = S.regs 0 → S'.regs 5 = S.regs 1 → S'.regs 6 = S.regs 2 →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl → S'.regs 9 = BitVec.ofNat 64 yc →
      S'.regs 10 = BitVec.ofNat 64 (lm - lo) → S'.regs 30 = BitVec.ofNat 64 recR → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hl64 : lm < 2 ^ 64 := by rw [← h200]; exact Memory.readLE_lt _ _ _
  have hlo64 : lo < 2 ^ 64 := by rw [← h96]; exact Memory.readLE_lt _ _ _
  have esub : BitVec.ofNat 64 lm - BitVec.ofNat 64 lo = BitVec.ofNat 64 (lm - lo) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  generalize e0 : S.regs 0 = x0 at K
  generalize e1 : S.regs 1 = x1 at K
  generalize e2 : S.regs 2 = x2 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e28 : S.regs 28 = x28 at K
  generalize e29 : S.regs 29 = x29 at K
  generalize eS : S.sp = xsp at K
  subst hmem
  janus_run [h200, h96, h144, h176, h184, h192, h120, h128, h136, hacc, hal, esub] until [fnE]
  refine K _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

/-- a slot read through a callee frame `R.rt ++ winA ++ [z] ++ stack ranges` (adapted from `slot_keep`) -/
theorem slotK {R : RtInv} {m m' : Memory} {sp stk' A' zp zc : Nat} {stw : List (Nat × Nat)}
    (h : MemFrame m m' (R.rt ++ [(sp - stk', sp - 8), (sp + 8, sp + A')] ++ [(zp, zp + 8 * zc)] ++ stw))
    {a : Nat} (ha : (a + 8 ≤ sp - stk' ∨ sp - 8 ≤ a) ∧ (a + 8 ≤ sp + 8 ∨ sp + A' ≤ a)) (hrt : Outside a 8 R.rt)
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- our slots `SP - 120`, `SP - 112` (FP/LR) and `SP - 16` (`lo`) survive the recursive call's frame -/
theorem keep3 {R : RtInv} {M2 M3 : Memory} {SP stk A zp zc st w l c : Nat}
    (hFc : MemFrame M2 M3 (R.rt ++ [(SP - 112 - (stk - 112), SP - 112 - 8), (SP - 112 + 8, SP - 112 + 96)] ++
      [(zp, zp + 8 * zc)] ++ [(st, st + 24), (w + 8 * l, w + 8 * c)]))
    (hk : 4320 ≤ stk) (hle : stk ≤ SP) (hA : 96 ≤ A) (hwin : Outside (SP - stk) (stk + A) R.rt)
    (hstw : Outside st 24 [(SP - stk, SP + A)]) (harr : 0 < c → Outside w (8 * c) [(SP - stk, SP + A)])
    (hcap0 : c = 0 → w = 0) (hlc : l ≤ c) (hzW : 0 < zc → Outside zp (8 * zc) [(SP - stk, SP + A)]) :
    M3.readLE (SP - 120) 8 = M2.readLE (SP - 120) 8 ∧ M3.readLE (SP - 112) 8 = M2.readLE (SP - 112) 8 ∧
      M3.readLE (SP - 16) 8 = M2.readLE (SP - 16) 8 := by
  simp only [outside_cons, outside_nil, and_true] at hstw harr hzW
  have hst : ∀ {a : Nat}, SP - stk ≤ a → a + 8 ≤ SP + A →
      ∀ q ∈ [(st, st + 24), (w + 8 * l, w + 8 * c)], q.2 ≤ q.1 ∨ a + 8 ≤ q.1 ∨ q.2 ≤ a := by
    intro a h1 h2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp only; omega
    · simp only
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · have := hcap0 h0; left; rw [this, h0]; omega
      · have := harr h0; right; omega
  have hz : ∀ {a : Nat}, SP - stk ≤ a → a + 8 ≤ SP + A → 0 < zc → a + 8 ≤ zp ∨ zp + 8 * zc ≤ a := by
    intro a h1 h2 h0; have := hzW h0; omega
  refine ⟨?_, ?_, ?_⟩ <;> refine slotK hFc ⟨by omega, by omega⟩ (hwin.of_sub (by omega) (by omega))
    (hz (by omega) (by omega)) (hst (by omega) (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the slots of `M1` -/
theorem m1_rd (s : State) {zp zl zc st yp yl yc lm xp lo : Nat} (hsp1 : 8 ≤ s.sp.toNat - 112)
    (hz : zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ yp < 2 ^ 64 ∧ yl < 2 ^ 64 ∧ yc < 2 ^ 64 ∧
      lm < 2 ^ 64) (hlo : lo < 2 ^ 64) :
    let M := M1 s zp zl zc st yp yl yc lm xp lo
    let sp := s.sp.toNat - 112
    M.readLE (sp + 96) 8 = lo ∧ M.readLE (sp + 120) 8 = zp ∧ M.readLE (sp + 128) 8 = zl ∧
      M.readLE (sp + 136) 8 = zc ∧ M.readLE (sp + 144) 8 = st ∧ M.readLE (sp + 176) 8 = yp ∧
      M.readLE (sp + 184) 8 = yl ∧ M.readLE (sp + 192) 8 = yc ∧ M.readLE (sp + 200) 8 = lm ∧
      M.readLE (sp - 8) 8 = (s.regs 29).toNat ∧ M.readLE sp 8 = (s.regs 30).toNat := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hz
  intro M sp
  have h29 := BitVec.isLt (s.regs 29)
  have h30 := BitVec.isLt (s.regs 30)
  simp (disch := omega) only [M, sp, M1, W1, W0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    Nat.mod_eq_of_lt z1, Nat.mod_eq_of_lt z2, Nat.mod_eq_of_lt z3, Nat.mod_eq_of_lt z4, Nat.mod_eq_of_lt z5,
    Nat.mod_eq_of_lt z6, Nat.mod_eq_of_lt z7, Nat.mod_eq_of_lt z8, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt h29,
    Nat.mod_eq_of_lt h30]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem bud_sub {b b1 m c : Nat} (h : b - m ≤ b1) : b - (m + c) ≤ b1 - c := by omega

theorem le_sub112 {k : Nat} (h : 4320 ≤ k) : k - 112 + 112 ≤ k := by omega

/-- `CPre` with a smaller budget claim -/
theorem cpre_cst {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
    {need cst c : Nat} {s : State} (h : NHyp.CPre R b L stk A zp zl zc st ins need cst s) (hc : c ≤ cst) :
    NHyp.CPre R b L stk A zp zl zc st ins need c s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, hcb, hinv⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    Nat.le_trans hc hcb, hinv⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the recursive call** (see the module doc) -/
theorem recCall {impl : List Segment} {cf : Nat → Nat → Nat} {lm' : Nat}
    (hO : ∀ (b1 : Nat) (L1 : List (Nat × Nat)) (p1 l1 c1 : Nat), p1 < 2 ^ 64 → c1 < 2 ^ 64 →
      Summary (LibW.program.link impl) fnE
        (fun s1 => Regs s1 zp zl zc st p1 l1 c1 yp yl yc lm' ∧
          PreD R b1 L1 (stk - 112) 96 (cf (stLen s1.mem st) lm') zp zl zc st p1 l1 yp yl lm' s1 ∧
          natVal s1.mem p1 l1 % 2 = 1 ∧ (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48)
        (fun s1 s' => PostD R b1 L1 (stk - 112) 96 (cf (stLen s1.mem st) lm') zp zc st
          (natVal s1.mem p1 l1 ^ natVal s1.mem yp yl % 2 ^ lm') s1 s'))
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    {tz lo : Nat} (hlo : lo < lm) (hlm' : lm' = lm - lo) (htz : tz = Exp.tz (natVal s.mem xp xl))
    (hbud : makeCost (Rsh.need xl tz) + cf (stLen s.mem st) lm' ≤ cst)
    (hz : zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ yp < 2 ^ 64 ∧ yl < 2 ^ 64 ∧ yc < 2 ^ 64 ∧
      lm < 2 ^ 64)
    {stkR aboveR : Nat} (hkR : stkR + 112 ≤ stk) (haR : aboveR ≤ 88) {Q : State → Prop}
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 112))
    (r28 : S.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat) (r18 : S.regs 18 = s.regs 18)
    (r29 : S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 120)) (hm : S.mem = M1 s zp zl zc st yp yl yc lm xp lo)
    (S1 : State) (h1pc : S1.pc = BitVec.ofNat 64 rshR) (h1sp : S1.sp = S.sp) (h128 : S1.regs 28 = S.regs 28)
    (h129 : S1.regs 29 = S.regs 29) (h118 : S1.regs 18 = S.regs 18) (h1rg : S1.mem.regions = S.mem.regions)
    (hq : Rsh.RshPost R b L stkR aboveR 0 0 xp xl tz S S1)
    (K : ∀ S3 : State, S3.pc = BitVec.ofNat 64 recR → S3.sp = BitVec.ofNat 64 (s.sp.toNat - 112) →
      S3.regs 18 = s.regs 18 → S3.regs 28 = s.regs 28 → S3.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 120) →
      S3.mem.regions = s.mem.regions → S3.mem.readLE (s.sp.toNat - 16) 8 = lo →
      S3.mem.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat → S3.mem.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat →
      NHyp.CPostR R b L stk A zp zc st ((natVal s.mem xp xl / 2 ^ tz) ^ natVal s.mem yp yl % 2 ^ lm')
        (makeCost (Rsh.need xl tz) + cf (stLen s.mem st) lm') s S3 →
      ReachesRet (LibW.program.link impl) (s.regs 30) S3 Q) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S1 Q := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hz
  obtain ⟨hC, hX, hY, -, hlm, hst0, op, hone, hsa⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hal, hle, h48, hacc⟩, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, ⟨-, hzL, hzW⟩, hins, hsok, hstw, -, harr,
    hcap0, hneed, -, -, -, -, -, -, hcb, -⟩ := hC'
  obtain ⟨⟨-, hxa, hx48, hxH, hxw⟩, hxn, -⟩ := hins xp xl (by simp)
  obtain ⟨⟨-, hya, hy48, hyH, hyw⟩, hyn, -⟩ := hins yp yl (by simp)
  generalize hSP : s.sp.toNat = SP at *
  have hSs : S.sp.toNat = SP - 112 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  -- frames from the entry
  have hF0 : MemFrame s.mem S.mem (ownW s stk A) := by rw [hm]; exact m1_frame s (by omega) (by omega) hA
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF0 : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hF0 hLs'
  obtain ⟨p1, l1, c1, q0, q1, q2, L1, b1, hres, hcap, ⟨hx, hb1, hinv⟩, hF, hLF⟩ := hq
  simp only [winA, hSs] at hF
  have hFs : MemFrame s.mem S1.mem (R.rt ++ ownW s stk A) := hF0.trans hF fun a k ho => by
    simp only [ownW, hSP, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1, h2⟩ := ho
    refine ⟨⟨h1, h2⟩, ?_⟩
    simp only [and_assoc]
    exact ⟨hrt, by omega, by omega, by omega⟩
  have hLFs : LiveFrame s.mem S1.mem L [] :=
    hLF0.trans ⟨fun a n hin _ => hLF.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
      fun _ _ h => h
  have hrgs : S1.mem.regions = s.mem.regions := by rw [h1rg, hm]; exact m1_regions s _ _ _ _ _ _ _ _ _ _
  -- the slots at the call
  have slot : ∀ a, SP - 16 ≤ a → a + 8 ≤ SP + 96 → S1.mem.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 =>
    hF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true, and_assoc]
      exact ⟨hwin.of_sub (by omega) (by omega), by omega, by omega, by omega⟩)
  have hM1 := m1_rd s (zp := zp) (zl := zl) (zc := zc) (st := st) (yp := yp) (yl := yl) (yc := yc) (lm := lm)
    (xp := xp) (lo := lo) (by omega) ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ (by omega)
  simp only [hSP] at hM1
  have sv : ∀ {o v : Nat}, v < 2 ^ 64 → (o = 96 ∧ v = lo) ∨ (o = 120 ∧ v = zp) ∨ (o = 128 ∧ v = zl) ∨
      (o = 136 ∧ v = zc) ∨ (o = 144 ∧ v = st) ∨ (o = 176 ∧ v = yp) ∨ (o = 184 ∧ v = yl) ∨ (o = 192 ∧ v = yc) ∨
      (o = 200 ∧ v = lm) → S1.mem.readLE (SP - 112 + o) 8 = v := by
    intro o v hv ho
    rw [slot _ (by omega) (by omega), hm]
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hM1.1
    · exact hM1.2.1
    · exact hM1.2.2.1
    · exact hM1.2.2.2.1
    · exact hM1.2.2.2.2.1
    · exact hM1.2.2.2.2.2.1
    · exact hM1.2.2.2.2.2.2.1
    · exact hM1.2.2.2.2.2.2.2.1
    · exact hM1.2.2.2.2.2.2.2.2.1
  have hlo64 : lo < 2 ^ 64 := by omega
  have hsp1 : 8 ≤ SP - 112 := by omega
  have f1 : S1.mem.readLE (SP - 16) 8 = lo := by rw [show SP - 16 = SP - 112 + 96 by omega]; exact sv hlo64 (by simp)
  have f23 : S1.mem.readLE (SP - 120) 8 = (s.regs 29).toNat ∧ S1.mem.readLE (SP - 112) 8 = (s.regs 30).toNat := by
    have e : ∀ a, SP - 120 ≤ a → a + 8 ≤ SP - 104 → S1.mem.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 =>
      hF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, and_assoc]
        exact ⟨hwin.of_sub (by omega) (by omega), by omega, by omega, by omega⟩)
    rw [e _ (by omega) (by omega), e _ (by omega) (by omega), hm, show SP - 120 = SP - 112 - 8 by omega]
    exact ⟨hM1.2.2.2.2.2.2.2.2.2.1, hM1.2.2.2.2.2.2.2.2.2.2⟩
  -- the fresh `xOdd`
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  obtain ⟨hts, hto⟩ := Exp.tz_spec hX
  rw [← htz] at hts hto
  have h2tz : 2 ^ tz ≤ natVal s.mem xp xl := by
    exact Nat.le_of_dvd hX ⟨_, hts⟩
  have htzl : tz < 64 * xl := by
    have := Nat.lt_of_le_of_lt h2tz (natVal_lt s.mem xp xl)
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
  have hneed0 : 0 < Rsh.need xl tz := by simp only [Rsh.need]; omega
  obtain ⟨hv1, hn1, hlc1, hc140, hlive1, -, hfr1⟩ := hres
  have hc1 : Rsh.need xl tz ≤ c1 := hcap hneed0
  obtain ⟨hin1, hap1⟩ := hfr1 hneed0 (by omega)
  obtain ⟨hp8, hH1, hacc1, hp48⟩ := hlive1 (by omega)
  have hvxS : natVal S.mem xp xl = natVal s.mem xp xl :=
    hxH.readLE (hF0.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) (LiveFrame.of_nil' hLF0 _) (by
      simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hxw ⊢; omega)
  rw [hvxS] at hv1
  have hl1 : l1 ≤ xl := lenLe hn1 (by
    rw [hv1]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (natVal_lt s.mem xp xl))
  -- the run to the recursive entry
  have hacc2 : S1.mem.accessible (SP - 112 + 96) 112 false = true := by
    rw [hFs.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
  refine runRec (s.regs 30) Q (SP - 112) zp zl zc st yp yl yc lm lo S1.mem (by omega) (by omega) hacc2
    (sv z8 (by simp)) (sv hlo64 (by simp)) (sv z4 (by simp)) (sv z5 (by simp)) (sv z6 (by simp)) (sv z7 (by simp))
    (sv z1 (by simp)) (sv z2 (by simp)) (sv z3 (by simp)) (by omega) S1 h1pc (h1sp.trans hsp) rfl ?_
  intro S2 f0 fsp fm a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a30 a18 a28 a29
  have hS2s : S2.sp.toNat + 112 = SP := by rw [fsp, h1sp, hSs]; omega
  have e28 : S2.regs 28 = s.regs 28 := by rw [a28, h128, r28]; simp
  have hF2 : MemFrame s.mem S2.mem (R.rt ++ ownW s stk A) := by rw [fm]; exact hFs
  have hLF2 : LiveFrame s.mem S2.mem L [] := by rw [fm]; exact hLFs
  have hstO : Outside st 24 (ownW s stk A) := by
    simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF2 hLF2 hstO
  have hp64 : p1 < 2 ^ 64 := by omega
  have hc64 : c1 < 2 ^ 64 := by omega
  have hvy : natVal S2.mem yp yl = natVal s.mem yp yl :=
    hyH.readLE hF2 (LiveFrame.of_nil' hLF2 _) (by
      simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at hyw ⊢; omega)
  have hvx : natVal S2.mem p1 l1 = natVal s.mem xp xl / 2 ^ tz := by rw [fm]; exact hv1
  -- the fresh input's facts at the callee entry
  have hAw : ∀ {a n : Nat}, Held R L a n → Apart p1 (8 * l1) a n := fun h =>
    apart_sub (apF hin1 hap1 h) (Nat.le_refl _) (by omega)
  have hin : ∀ p n, (p, n) ∈ [(p1, l1), (yp, yl)] → RdIn R L1 S2 (stk - 112) 96 p n ∧ n ≤ 2 ^ 9 ∧
      NatNorm S2.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (NHyp.freeOf S2.mem st).1 (NHyp.freeOf S2.mem st).2 ∧
      (0 < zc → Apart zp (8 * zc) p (8 * n)) := by
    intro p n hpn
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpn
    rcases hpn with ⟨hp, hn⟩ | ⟨hp, hn⟩ <;> rw [hp, hn]
    · refine ⟨⟨by omega, by
          rw [fm]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc1 (Nat.le_refl _) (by omega)),
        by omega, hH1.sub (Nat.le_refl _) (by omega), ?_⟩, by omega, by rw [fm]; exact hn1, hAw hsok.2.1, ?_, ?_⟩
      · have := (hin1.apart hwin)
        simp only [win, hS2s, outside_cons, outside_nil, and_true]; unfold Apart at this; omega
      · show Apart p1 (8 * l1) (stW S2.mem st + 8 * stLen S2.mem st) (8 * (stCap S2.mem st - stLen S2.mem st))
        rw [ew, el, ec]
        rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
        · have := hcap0 h0; have := hsok.2.2.2.2.2.1; unfold Apart; omega
        · have := hAw (hsok.2.2.2.2.1 h0).2.1; unfold Apart at this ⊢; omega
      · intro h0; exact (hAw (hzL h0).2.1).symm
    · exact in_sub hC (p := yp) (n := yl) (by simp) hF2 hLF2 hx (by omega) (by omega) (by omega)
  have hone2 := natOne_subR hC hone hsa hF2 hLF2 hx (by omega) (stk' := stk - 112) (A' := 96) (by omega) (by omega)
    ew el ec
  have hcf : cf (stLen S2.mem st) lm' ≤ b1 := by rw [el]; omega
  have hinv2 : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S2.mem) := by
    rw [fm]; rw [r28, tN (BitVec.isLt _)] at hinv; exact hinv
  have hpre : PreD R b1 L1 (stk - 112) 96 (cf (stLen S2.mem st) lm') zp zl zc st p1 l1 yp yl lm' S2 :=
    ⟨cpre_sub hC hF2 hLF2 (by rw [fm]; exact hrgs) hx hinv2 (by omega) e28 (by omega) (by omega) hin (by omega) hcf,
      by rw [hvx]; omega, by rw [hvy]; exact hY, by omega, by omega, hst0, op, hone2⟩
  have hS := hO b1 L1 p1 l1 c1 hp64 hc64
  have hbb : b - (makeCost (Rsh.need xl tz) + cf (stLen s.mem st) lm') ≤ b1 - cf (stLen s.mem st) lm' := bud_sub hb1
  have hcap0' := hcap0
  have hkk : stk - 112 + 112 ≤ stk := le_sub112 hk
  have hSsp2 : S2.sp.toNat + 112 = s.sp.toNat := hS2s.trans hSP.symm
  have hlcS := hsok.2.2.2.2.2.1
  have hstw' := hstw
  simp only [win, hSP] at hstw'
  have harr' : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) [(SP - stk, SP + A)] := fun h => by
    have := (harr h).1; simp only [win, hSP] at this; exact this
  have hzW' : 0 < zc → Outside zp (8 * zc) [(SP - stk, SP + A)] := fun h => by
    have := (hzW h).1; simp only [win, hSP] at this; exact this
  have e30 : (S2.regs 30).toNat = recR := by rw [a30]; rfl
  have hR2 : Regs S2 zp zl zc st p1 l1 c1 yp yl yc lm' :=
    ⟨a0, a1, a2, a3, a4.trans q0, a5.trans q1, a6.trans q2, a7, a8, a9, by rw [a10, hlm']⟩
  have hodd : natVal S2.mem p1 l1 % 2 = 1 := by rw [hvx]; exact hto
  have hr4 : (S2.regs 30).toNat % 4 = 0 := by rw [e30]; decide
  have hr48 : (S2.regs 30).toNat < 2 ^ 48 := by rw [e30]; decide
  refine ReachesRet.call_regions hS f0 ⟨hR2, hpre, hodd, hr4, hr48⟩ fun S3 h3pc hq3 h3rg => ?_
  obtain ⟨g1, g2, g3, g4, hcp⟩ := hq3
  rw [hvx, hvy, el] at hcp
  have hcp' := hcp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hFc, -⟩ := hcp'
  have hS2' : S2.sp.toNat = SP - 112 := Nat.eq_sub_of_add_eq hS2s
  simp only [winA, hS2', stWs, stkWs, ew, el, ec] at hFc
  obtain ⟨k1, k2, k3⟩ := keep3 hFc hk hle hA hwin hstw' harr' hcap0' hlcS hzW'
  refine K S3 (h3pc.trans a30) (g1.trans (fsp.trans (h1sp.trans hsp))) (g2.trans (a18.trans (h118.trans r18)))
    (g3.trans e28) (g4.trans (a29.trans (h129.trans r29))) (h3rg.trans (by rw [fm]; exact hrgs))
    (by rw [k3, fm]; exact f1) (by rw [k1, fm]; exact f23.1) (by rw [k2, fm]; exact f23.2) ?_
  exact cpost_pre (cpre_cst hC hbud) hF2 hLF2 hx hSsp2 e28 (stk' := stk - 112) (A' := 96) hkk (by decide) hbb hcp
    rfl rfl rfl rfl


end

end FvModexp.Arm64.P2D
