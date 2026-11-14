import FvModexp.Proofs.Amd64.Exp.P2DLshR
import FvModexp.Proofs.Amd64.Exp.P2DRet
import FvModexp.Proofs.Amd64.Exp.P2DRsh

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `return z.lsh(z, lo)` (nat.go:955; agent asm s71; twin of infra's arm64 `P2DLsh`)

`lshPath`: from `recR` (the recursive call's exit facts at the entry level: `RSP = SP - 0x70`, result `(p2, l2, c2)`
of value `v1`, `0 < v1 < 2^lm'`) through `runL`, `Lsh.Hyp2` (`z = x = (p2, l2, c2)`, `sh = lo`; callee `RSP = SP - 0x78`,
window `[RSP - stkL, RSP + aboveL)` inside ours) and `epiL` to the function's exit: `PostD` with value `v1 · 2^lo` and
cost `cst1 + makeCost (lm / 64 + 2)` (`lsh` needs `l2 + lo/64 + 1 ≤ lm/64 + 2` words).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp FvModexp.Amd64.EvenHyp

theorem mk_mono {a k : Nat} (h : a ≤ k) (hk : 2 ≤ k) : makeCost a ≤ makeCost k := by
  unfold makeCost makeCap allocCost; split <;> split <;> omega

theorem outF {b k : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, b + k ≤ r.1 ∨ r.2 ≤ b) → Outside b k rs
  | [], _ => trivial
  | (lo, hi) :: rs, h => ⟨h (lo, hi) List.mem_cons_self, outF fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- a frame ignores the empty ranges of its write set -/
theorem frame_ne {m m' : Memory} {rs ws : List (Nat × Nat)} (h : MemFrame m m' (rs ++ ws)) :
    MemFrame m m' (rs ++ ws.filter fun r => decide (r.1 < r.2)) :=
  ⟨fun a n ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      rw [outside_append] at ho
      have := h.readLE (a + i) 1 (by
        rw [outside_append]
        refine ⟨ho.1.of_sub (by omega) (by omega), outF fun r hr => ?_⟩
        by_cases hlt : r.1 < r.2
        · have := MemFrame.outside_mem ho.2 (List.mem_filter.2 ⟨hr, by simpa using hlt⟩); omega
        · omega)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm), h.accessible⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the entry ranges a callee may have written: accessible at entry, and (when non-empty) apart from the guard word
and the TLS slot -/
theorem ws_facts (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) :
    (∀ r ∈ win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st, r.1 < r.2 →
      s.mem.accessible r.1 (r.2 - r.1) true = true) ∧
    (∀ r ∈ win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st, r.1 < r.2 →
      ((s.regs 14).toNat + 16 + 8 ≤ r.1 ∨ r.2 ≤ (s.regs 14).toNat + 16) ∧
      (s.fsBase.toNat - 8 + 8 ≤ r.1 ∨ r.2 ≤ s.fsBase.toNat - 8)) := by
  have ce0 := cenv_ent hP.1
  obtain ⟨-, hK0, -, hacc, -, -, -, -, hga, -, -, -, -, -, -, -, -, -, f6⟩ := ce0
  obtain ⟨-, -, -, -, -, -, ⟨-, hzL, hzW⟩, -, hsok, -, hstg, harr, -, -, -, -, -, ⟨hstf, -⟩, -, -, -, -, -, harf,
    -⟩ := hP
  have hlc := hsok.2.2.2.2.2.1
  unfold Apart at hga f6 hstg hstf
  refine ⟨fun r hr h12 => ?_, fun r hr h12 => ?_⟩
  all_goals
    simp only [win, stWs, stkWs, List.append_assoc, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl <;> simp only at h12 ⊢
    · exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    · rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact (hzL (by omega)).2.2.1
    · rw [show st + 24 - st = 24 by omega]; exact hsok.2.2.1
    · have h0 : 0 < stCap s.mem st := by omega
      exact Janus.Arm64.Memory.accessible_mono _ (hsok.2.2.2.2.1 h0).2.2.1 (by omega) (by omega)
  · rcases hr with rfl | rfl | rfl | rfl <;> simp only at h12 ⊢
    · constructor <;> omega
    · have h0 : 0 < zc := by omega
      have a1 := (hzW h0).2.1; have a2 := (hzW h0).2.2; unfold Apart at a1 a2; constructor <;> omega
    · constructor <;> omega
    · have h0 : 0 < stCap s.mem st := by omega
      have a1 := (harr h0).2; have a2 := harf h0; unfold Apart at a1 a2; constructor <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the caller environment at the `lsh` call (after the recursive call and the return-address push) -/
theorem cenvL (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {M : Memory}
    (hF : MemFrame s.mem M (R.rt ++ win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st))
    (hrg : M.regions = s.mem.regions) {L1 : List (Nat × Nat)} (hx : LiveExt R L L1) (hk : 0x78 ≤ stk) (v : Nat) :
    CallW.CEnv R L1 (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x78) (stk - 0x78) (0x78 + A)
      (M.writeLE ((s.regs 4).toNat - 0x78) 8 v) := by
  obtain ⟨hws, hgf⟩ := ws_facts hP
  have ce0 := cenv_ent hP.1
  have hF' : MemFrame s.mem M (R.rt ++ (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st)) := by
    simpa only [List.append_assoc] using hF
  have hFn := frame_ne hF'
  generalize hW : win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st = ws at hws hgf hFn
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := id ce0
  generalize hSP : (s.regs 4).toNat = SP at *
  have hwm : (SP - stk, SP + A) ∈ ws := by rw [← hW]; simp [win, hSP]
  have hFw : MemFrame s.mem (M.writeLE (SP - 0x78) 8 v) (R.rt ++ ws.filter fun r => decide (r.1 < r.2)) :=
    hFn.writeLE v (List.mem_append_right _ (List.mem_filter.2 ⟨hwm, by simp only [decide_eq_true_eq]; omega⟩))
      (by simp only; omega) (by simp only; omega)
  have ce1 := CallW.CEnv.frame ce0 hFw (by simp only [Janus.Arm64.Memory.regions_writeLE]; exact hrg)
    (fun r hr h12 => hws r (List.mem_filter.1 hr).1 h12)
    (outF fun r hr => by
      have h12 : r.1 < r.2 := by simpa using (List.mem_filter.1 hr).2
      have := (hgf r (List.mem_filter.1 hr).1 h12).1; omega)
    (outF fun r hr => by
      have h12 : r.1 < r.2 := by simpa using (List.mem_filter.1 hr).2
      have := (hgf r (List.mem_filter.1 hr).1 h12).2; omega)
  exact cenv_ext (cenv_rebase ce1 (x' := SP - 0x78) (K' := stk - 0x78) (A' := 0x78 + A) (by omega)
    (by omega) (by omega) (by omega)) hx

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- where the recursive result lies: apart from our window, the guard word and the TLS slot -/
theorem locP (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {L2 : List (Nat × Nat)} {M : Memory}
    {p2 l2 c2 v : Nat} (hr : NatOF R L L2 M zp zc 1 p2 l2 c2 v) (hc0 : 0 < c2) :
    Apart p2 (8 * c2) ((s.regs 4).toNat - stk) (stk + A) ∧ Apart p2 (8 * c2) ((s.regs 14).toNat + 16) 8 ∧
      Apart p2 (8 * c2) (s.fsBase.toNat - 8) 8 := by
  have ce0 := cenv_ent hP.1
  obtain ⟨-, hK0, -, -, -, -, -, hrt, -, hgrt, -, -, -, -, -, -, -, f5, -⟩ := ce0
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hzW⟩, -⟩ := hP
  obtain ⟨-, -, -, -, -, hloc⟩ := hr
  rcases hloc with ⟨e1, e2⟩ | ⟨-, hin, -⟩
  · subst e1 e2
    obtain ⟨h1, h2, h3⟩ := hzW hc0
    simp only [win, outside_cons, outside_nil, and_true] at h1
    exact ⟨by unfold Apart; omega, h2, h3⟩
  · exact ⟨(hin.apart hrt).symm, (hin.apart hgrt).symm, (hin.apart f5).symm⟩

end

/-- numeric facts of the `lsh` call -/
theorem nL2 {l2 lm lm' lo : Nat} (hl2 : l2 ≤ (lm' + 63) / 64) (hlm' : lm' + lo ≤ lm) (hlm : lm ≤ 2 ^ 13) :
    l2 + lo / 64 + 1 ≤ lm / 64 + 2 ∧ 2 ≤ lm / 64 + 2 ∧ l2 + lo / 64 + 1 ≤ 2 ^ 16 ∧ 1 ≤ l2 + lo / 64 + 1 := by
  omega

theorem nSL {SP : Nat} (h1 : 0x78 ≤ SP) (h2 : SP < 2 ^ 64) :
    BitVec.ofNat 64 (SP - 0x78) + 8#64 = BitVec.ofNat 64 (SP - 0x70) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem cwL {a k SP stk A stkL aboveL : Nat} (hkL : stkL + 0x78 ≤ stk) (haL : aboveL ≤ 0x60) (hle : stk ≤ SP)
    (h : Outside a k [(SP - stk, SP + A)]) (hA : 96 ≤ A) :
    Outside a k [(SP - 0x78 - stkL, SP - 0x78 + aboveL), (SP - 0x78, SP - 0x78 + 8)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

theorem slotO {R : RtInv} {SP stk A stkL aboveL p2 c2 a : Nat} (hwin : Outside (SP - stk) (stk + A) R.rt)
    (hp : Apart p2 (8 * c2) (SP - stk) (stk + A)) (hkL : stkL + 0x78 ≤ stk) (haL : aboveL ≤ 0x60)
    (hle : stk ≤ SP) (hA : 96 ≤ A) (h1 : SP - 8 ≤ a) (h2 : a + 8 ≤ SP + 8) :
    Outside a 8 (R.rt ++ [(SP - 0x78 - stkL, SP - 0x78 + aboveL), (SP - 0x78, SP - 0x78 + 8)] ++
      [(p2, p2 + 8 * c2)]) := by
  simp only [outside_append, outside_cons, outside_nil, and_true]
  unfold Apart at hp
  exact ⟨⟨hwin.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl yp yl lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `lsh` call and the exit** (see the module doc) -/
theorem lshPath {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains NHyp.fnP2 = false)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL + 0x78 ≤ stk) (haL : aboveL ≤ 0x60)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (hret : (retAddrOf s).toNat < 2 ^ 47)
    {lo lm' v1 cst1 w : Nat} (hlo0 : 0 < lo) (hlm' : lm' + lo ≤ lm) (hv0 : 0 < v1) (hvb : v1 < 2 ^ lm')
    (hw : v1 * 2 ^ lo = w) (hbud : cst1 + makeCost (lm / 64 + 2) ≤ cst)
    (S3 : State) (h3pc : S3.rip = BitVec.ofNat 64 recR) (h3sp : S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x70))
    (h314 : S3.regs 14 = s.regs 14) (h3x : S3.xmm 15 = s.xmm 15) (h3rg : S3.mem.regions = s.mem.regions)
    (f1 : S3.mem.readLE ((s.regs 4).toNat - 0x70 + 0x58) 8 = lo)
    (f2 : S3.mem.readLE ((s.regs 4).toNat - 0x70 + 0x68) 8 = (s.regs 5).toNat)
    (f3 : S3.mem.readLE ((s.regs 4).toNat - 0x70 + 0x70) 8 = (retAddrOf s).toNat)
    (hcp : NHyp.CPostR R b L stk A zp zc st v1 cst1 s S3) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S3 (PostD R b L stk A cst zp zc st w s) := by
  have hP0 := hP
  obtain ⟨hC, -, -, -, hlm, -, -, -, -⟩ := hP
  have hC' := hC
  obtain ⟨-, hsv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcb, -, -, -⟩ := hC'
  have ce0 := cenv_ent hC.1
  obtain ⟨-, hK0, hA0, hacc, -, -, -, hwin, -, -, -, -, -, -, -, -, -, -, -⟩ := ce0
  obtain ⟨hfs1, hdf1, p2, l2, c2, q0, q3, q1, L2, b2, hres, ⟨hx2, hb2, hinv2⟩, hsb, hF1, hLF1, hrs⟩ := hcp
  have hres0 := hres
  obtain ⟨hv, hn, hlc, hc40, hlive, -⟩ := hres0
  -- the recursive result
  have hl2 : l2 ≤ (lm' + 63) / 64 := lenLe hn (by
    rw [hv]; exact Nat.lt_of_lt_of_le hvb (Nat.pow_le_pow_right (by decide) (by omega)))
  have hl20 : 0 < l2 := by
    rcases Nat.eq_zero_or_pos l2 with h | h
    · subst h; simp [natVal] at hv; omega
    · exact h
  obtain ⟨hnd, hnd2, hnd16, hnd1⟩ := nL2 hl2 hlm' hlm
  have hmk : makeCost (l2 + lo / 64 + 1) ≤ makeCost (lm / 64 + 2) := mk_mono hnd hnd2
  have hc0 : 0 < c2 := by omega
  obtain ⟨hp8, hpH, hpacc, hp48⟩ := hlive hc0
  obtain ⟨hpW, hpG, hpF⟩ := locP hC hres hc0
  have hce := cenvL hC hF1 h3rg hx2 (by omega) lshR
  have hS64 := (s.regs 4).isLt
  generalize hSP : (s.regs 4).toNat = SP at *
  -- `runL` to the `lsh` entry
  have hacc3 : S3.mem.accessible (SP - 0x70 - 8) 0xd8 true = true := by
    rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  refine runL (retAddrOf s) _ (SP - 0x70) lo S3.mem (by omega) (by omega) hacc3 f1 S3 h3pc h3sp rfl ?_
  intro S' f0 fsp r0 r3 r1 r7 r6 r8 r9 r14 rfs rx rdf fm
  rw [show SP - 0x70 - 8 = SP - 0x78 by omega] at fsp fm
  have hS'sp : (S'.regs 4).toNat = SP - 0x78 := by rw [fsp, BitVec.toNat_ofNat]; omega
  have e14 : S'.regs 14 = s.regs 14 := r14.trans h314
  have hS := LibCalls.hypSumW hap hns
    (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (hlh b2 L2 (BitVec.ofNat 64 p2) (BitVec.ofNat 64 l2) (BitVec.ofNat 64 c2) (BitVec.ofNat 64 p2)
      (BitVec.ofNat 64 l2) (BitVec.ofNat 64 c2) (BitVec.ofNat 64 lo))
  rw [lsh_a] at hS
  have tp := LibCalls.tN (show p2 < 2 ^ 64 by omega)
  have tl := LibCalls.tN (show l2 < 2 ^ 64 by omega)
  have tc := LibCalls.tN (show c2 < 2 ^ 64 by omega)
  have tlo := LibCalls.tN (show lo < 2 ^ 64 by omega)
  simp only [tp, tl, tc, tlo] at hS
  have hwo : Outside p2 (8 * c2) (win S' stkL aboveL) := by
    simp only [win, hS'sp, outside_cons, outside_nil, and_true]; unfold Apart at hpW; omega
  have hg' : (S'.regs 14).toNat = (s.regs 14).toNat := by rw [e14]
  have hf' : S'.fsBase.toNat = s.fsBase.toNat := by rw [rfs, hfs1]
  have hra : S'.mem.readLE (S'.regs 4).toNat 8 = lshR := by
    rw [hS'sp, fm, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by decide)
  have hWf : MemFrame S3.mem S'.mem [(SP - 0x78, SP - 0x78 + 8)] := by
    rw [fm]; exact MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (Nat.le_refl _)
  have hvS : natVal S'.mem p2 l2 = v1 := by
    rw [← hv]
    exact hWf.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; unfold Apart at hpW; omega)
  have hinvS : R.inv b2 L2 (S'.regs 14).toNat (view R.rt L2 S'.mem) := by
    rw [hg']
    refine Expmc.inv_frame hWf (fun r hr => Or.inr ?_) hinv2
    simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hwin.of_sub (by omega) (by omega)
  refine ReachesRet.call_regions hS (by rw [f0]) ⟨?_, rx.trans (h3x.trans hx15), ?_,
      rdf.trans (hdf1.trans hdf), ?_⟩ fun s'' hr hq hrg' => ?_
  · rw [hra]; exact ra_p2 hap hnf 0x288 (by decide)
  · simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0.trans q0, r3.trans q3, r1.trans q1, r7.trans q0, r6.trans q3, r8.trans q1, r9, trivial⟩
  · refine ⟨⟨CallW.callEnv_of hce hS'sp hg' hf' fm (by omega) (by omega) (by omega), hsv, hlc,
      ⟨hc40, fun h => ?_, fun _ => ⟨hwo, by rw [hg']; exact hpG, by rw [hf']; exact hpF⟩⟩,
      ⟨by omega, by
        rw [fm, Janus.Arm64.Memory.accessible_writeLE]
        exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _)
          (by omega)), by omega, hpH.sub (Nat.le_refl _) (by omega), hwo.of_sub (Nat.le_refl _) (by omega)⟩,
      hnd16, Or.inl rfl, ?_, hinvS⟩, hlo0, hl20⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hlive h
      exact ⟨a1, a2, by rw [fm, Janus.Arm64.Memory.accessible_writeLE]; exact a3, a4⟩
    · have := Nat.le_trans hmk (Nat.le_trans (Nat.le_sub_of_add_le' hbud) (Nat.le_trans (Nat.sub_le_sub_right hcb _)
        hb2))
      exact this
  · obtain ⟨⟨e4, -, e14', ex⟩, qfs, qdf, p', l', c', a0, a3, a1, L3, b3, hres', hcap', ⟨hx3, hb3, hinv3⟩, hF2,
      hLF2⟩ := hq
    rw [hvS, hw] at hres'
    rw [hg'] at hinv3
    have hF3 : MemFrame S3.mem s''.mem (R.rt ++ [(SP - 0x78 - stkL, SP - 0x78 + aboveL), (SP - 0x78, SP - 0x78 + 8)] ++
        [(p2, p2 + 8 * c2)]) :=
      hWf.trans hF2 fun a n h => by
        simp only [win, hS'sp, outside_append, outside_cons, outside_nil, and_true] at h ⊢
        exact ⟨h.1.2.2, ⟨h.1.1, h.1.2.1⟩, h.2⟩
    have hLsW : LiveSep L2 [(SP - 0x78, SP - 0x78 + 8)] := fun r hr => by
      have := hce.2.2.2.2.2.2.2.2.2.2.1 r hr
      simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    have hLF3 : LiveFrame S3.mem s''.mem L2 [(p2, p2 + 8 * c2)] :=
      (LiveFrame.of_win hWf hLsW).trans hLF2 fun _ _ h => h
    have hrd : ∀ a, SP - 8 ≤ a → a + 8 ≤ SP + 8 → s''.mem.readLE a 8 = S3.mem.readLE a 8 := fun a h1 h2 =>
      hF3.readLE _ _ (slotO hwin hpW hkL haL hK0 hA h1 h2)
    have rbp : s''.mem.readLE (SP - 0x70 + 0x68) 8 = (s.regs 5).toNat := by
      rw [hrd _ (by omega) (by omega)]; exact f2
    have rra : s''.mem.readLE (SP - 0x70 + 0x70) 8 = (retAddrOf s).toNat := by
      rw [hrd _ (by omega) (by omega)]; exact f3
    have hacc' : s''.mem.accessible (SP - 0x70 + 0x68) 16 false = true := by
      rw [hF3.accessible, hF1.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    have hpc'' : s''.rip = BitVec.ofNat 64 lshR := by rw [hr]; simp only [retAddrOf, hra]
    have h4'' : s''.regs 4 = BitVec.ofNat 64 (SP - 0x70) := by
      rw [e4, fsp]; exact nSL (by omega) hS64
    refine epiL hpc'' h4'' (by omega) hacc' rbp rra hret fun s' hE b0 b3 b1 bm => ?_
    refine postD_of hP0 (by omega) hE (e14'.trans e14) (qfs.trans (rfs.trans hfs1)) (ex.trans (rx.trans h3x))
      (qdf.trans (rdf.trans hdf1)) fun hfs' hdf' => ?_
    have hcw : ∀ a k, Outside a k (win s stk A) →
        Outside a k [(SP - 0x78 - stkL, SP - 0x78 + aboveL), (SP - 0x78, SP - 0x78 + 8)] := fun a k h => by
      simp only [win, hSP] at h; exact cwL hkL haL hK0 h hA
    exact cpostR_lsh hC hres hx2 hb2 hsb hF1 hLF1 hrs hcw hres' hcap' hnd1 hx3 hb3 hinv3 hF3 hLF3
      (Nat.le_trans (Nat.add_le_add_left hmk _) hbud) bm (b0.trans a0) (b3.trans a3) (b1.trans a1) hfs' hdf'

end

end FvModexp.Amd64.P2D
