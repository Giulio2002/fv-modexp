import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsC1
import FvModexp.Proofs.Arm64.CmpSum

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsC2.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), correction loop: `e := qhatv.cmp(uu.norm())` (natdiv.go:833)

`c2`: from the `CALL nat.cmp` state of `c1` → `nat.cmp` (`CmpSum.cmp_summary` on `LibDrs`) → its return `0x1ba74c`
with `X0 = cmpQ |P| st` (as `BitVec.ofInt`), `Mc`/`V4`/the slot `i` kept.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

theorem cmpInt_range (a b : Nat) : Mdl.cmpInt a b = -1 ∨ Mdl.cmpInt a b = 0 ∨ Mdl.cmpInt a b = 1 := by
  unfold Mdl.cmpInt; split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

theorem cmpRev_range : ∀ (a b : List Nat), Mdl.cmpRev a b = -1 ∨ Mdl.cmpRev a b = 0 ∨ Mdl.cmpRev a b = 1
  | [], _ => by simp [Mdl.cmpRev]
  | [a], [] => by simp [Mdl.cmpRev]
  | [a], [b] => by simp only [Mdl.cmpRev]; exact cmpInt_range a b
  | [a], _ :: _ :: _ => by simp [Mdl.cmpRev]
  | _ :: _ :: _, [] => by simp [Mdl.cmpRev]
  | _ :: _ :: _, [_] => by simp [Mdl.cmpRev]
  | a :: a' :: xs, b :: b' :: ys => by
    simp only [Mdl.cmpRev]; split
    · exact cmpRev_range (a' :: xs) (b' :: ys)
    · exact cmpInt_range a b

theorem natCmp_range (x y : List Nat) : Mdl.natCmp x y = -1 ∨ Mdl.natCmp x y = 0 ∨ Mdl.natCmp x y = 1 := by
  unfold Mdl.natCmp; split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  · exact cmpRev_range _ _

/-- `nat.cmp` (segment 15) in `LibDrs.program` -/
theorem csumD (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDrs.program.link impl) cmpA CmpSum.Pre CmpSum.Post := by
  have hseg : FvModexp.Lib.CmpA64.program.segments = [Extracted.program.segments[15]'(by decide)] := rfl
  have hc := Callees.codeIn_single (lp := FvModexp.Lib.CmpA64.program) (ns := LibDrs.names) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 15) (by decide)) (by decide)
  rw [← LibDrs.eq_only] at hc
  exact Summary.of_codeIn hc CmpSum.cmp_summary

theorem lf_winX {L : List (Nat × Nat)} {X : State} {k a : Nat} {m m' : Memory} (ws : List (Nat × Nat))
    (h : MemFrame m m' (winA X k a)) (hs : LiveSep L (win X k a)) : LiveFrame m m' L ws :=
  ⟨fun x n hin _ => h.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hs r hr
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the loop's `nat.cmp` call**, from `c1`'s call state -/
theorem c2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (c : Cx) (s : State)
    (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St)
    (hC : C R c s Lk bk S j Z U qv i st) (Q : State → Prop)
    (X : State) (n' : Nat) (hpc : X.pc = BitVec.ofNat 64 cmpA) (hsp : X.sp = s.sp - 400#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rC1) (h0 : X.regs 0 = BitVec.ofNat 64 qv)
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.P s j U).length) (h2 : X.regs 2 = BitVec.ofNat 64 (3 * c.vl))
    (h3 : X.regs 3 = BitVec.ofNat 64 (c.uuP j)) (h4 : X.regs 4 = BitVec.ofNat 64 n')
    (hF1 : MemFrame S.mem X.mem (is1 s)) (hreg : X.mem.regions = S.mem.regions)
    (hsi : X.mem.readLE (s.sp.toNat - 160) 8 = i) (hi : i < 2) (hle : n' ≤ c.uuL j)
    (hv : natVal S.mem (c.uuP j) n' = natVal S.mem (c.uuP j) (c.uuL j)) (hN : NatNorm S.mem (c.uuP j) n')
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rC1 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 →
      T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st) →
      Mc R c s Lk bk T.mem j Z U qv st → V4 c s T.mem qv (c.P s j U).length →
      T.mem.readLE (s.sp.toNat - 160) 8 = i →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hmc0 := hC.mc
  have hcr := hmc0.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, -, huw, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have h40 := hcr.h40
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hmc := Mc.own1 hmc0 hF1 hreg
  have hv4 := V4.own1 hC.v4 hF1 h0'
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 24 40 := Ev.callEnv hcr hmc.ev hspn h28 (by omega) (by omega)
  obtain ⟨⟨g1, g2, g3⟩, hsk, -, hout, -, -, hLs, -⟩ := hce'
  have hPl : (c.P s j U).length ≤ 3 * c.vl := by
    have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
      ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
    rw [Mdl.length_toL, List.length_take] at h1
    have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
    have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
    show (Mdl.norm _).length ≤ _
    rw [List.length_take]
    omega
  have hqa := hmc.qa
  have hq48 := Memory.accessible_bound _ hqa
  have hqw := hmc.rg.w
  simp only [win, outside_cons, outside_nil, and_true] at hqw huw
  have eU : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → X.mem.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => hF1.readLE x n (by simp only [is1, outside_cons, outside_nil, and_true]; omega)
  have huacc : X.mem.accessible (c.uuP j) (8 * n') false = true := by
    rw [hmc.ev.fr.accessible]
    exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hua (by simp only [Cx.uuP]; omega)
      (by simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega))
  have t0 : (BitVec.ofNat 64 qv).toNat = qv := by rw [BitVec.toNat_ofNat]; omega
  have t1 : (BitVec.ofNat 64 (c.P s j U).length).toNat = (c.P s j U).length := by rw [BitVec.toNat_ofNat]; omega
  have t3 : (BitVec.ofNat 64 (c.uuP j)).toNat = c.uuP j := by
    rw [BitVec.toNat_ofNat]; simp only [Cx.uuP]; omega
  have t4 : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; simp only [Cx.uuL] at hle; omega
  have hpre : CmpSum.Pre X := by
    unfold CmpSum.Pre GuardOK CmpSum.SliceOK
    rw [h30, h0, h1, h3, h4, t0, t1, t3, t4]
    refine ⟨by decide, by decide, ⟨g1, g2, by omega⟩, hsk, ?_, ?_⟩
    · by_cases hz : (c.P s j U).length = 0
      · exact Or.inl hz
      · refine Or.inr ⟨Memory.accessible_read_of_write _ (Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega)), ?_⟩
        unfold Apart; omega
    · by_cases hz : n' = 0
      · exact Or.inl hz
      · refine Or.inr ⟨huacc, ?_⟩
        unfold Apart; simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega
  refine ReachesRet.call_regions (csumD impl hap) hpc hpre fun T hT hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  simp only [CmpSum.frame] at hf
  have hfw : MemFrame X.mem m (winA X 24 40) := hf.mono fun x n ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hMF : MemFrame X.mem m (R.rt ++ winA X 24 40 ++ [(0, 0)]) := hfw.mono fun x n ho => by
    simp only [outside_append] at ho; exact ho.1.2
  have hLF : LiveFrame X.mem m Lk [(0, 0)] := lf_winX _ hfw hLs
  have hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m) := by
    rw [← h28]; exact inv_frame_winA hfw hout (by omega) (by omega) (by rw [h28]; exact hmc.ev.inv)
  have hreg' : m.regions = X.mem.regions := hrg
  -- the reads of `qhatv` and `uu` across the call
  have kQ : m.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) :=
    hfw.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have o0 : ∀ x n, Outside x n [(0, 0)] := fun x n => by simp only [outside_cons, outside_nil, and_true]; omega
  have a0 : ∀ x n, Apart x n 0 0 := fun x n => by unfold Apart; omega
  have rw' : ∀ x n, (x + n ≤ s.sp.toNat - 424 ∨ s.sp.toNat - 360 ≤ x) → m.readLE x n = X.mem.readLE x n :=
    fun x n h => hfw.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have ht0w := hcr.t0w
  simp only [win, outside_cons, outside_nil, and_true] at ht0w
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have hmcT : Mc R c s Lk bk m j Z U qv st :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF (LiveExt.refl R Lk) hinv hreg' (Nat.le_refl _)
      (fun x n _ => o0 x n) (fun x n _ _ => o0 x n) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (a0 _ _) (a0 _ _) (a0 _ _) (a0 _ _) (a0 _ _)
      (by rw [limbs_congr (rw' _ _ (by omega))]; exact hmc.qk)
      (by rw [limbs_congr kQ]; exact hmc.bf)
      (by rw [limbs_congr (rw' _ _ (by omega))]; exact hmc.wk)
  -- the result
  have hlq : Asm.limbs X.mem qv (c.P s j U).length = st.buf.take (c.P s j U).length := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hPl]
  have hvX : natVal X.mem (c.uuP j) n' = natVal X.mem (c.uuP j) (c.uuL j) := by
    simp only [natVal]
    rw [eU (c.uuP j) (8 * n') (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega),
      eU (c.uuP j) (8 * c.uuL j) (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL]; omega)]
    exact hv
  have hNX : NatNorm X.mem (c.uuP j) n' := by
    rcases hN with h | h
    · exact Or.inl h
    · right; rw [eU _ _ (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL] at hle ⊢; omega)]; exact h
  have hlu : Asm.limbs X.mem (c.uuP j) n' = Mdl.norm st.w := Asm.limbs_norm hmc.wk hvX hNX
  have hres : CmpSum.cmpRes (c.P s j U).length n' (Asm.lv X.mem qv (c.P s j U).length) (Asm.lv X.mem (c.uuP j) n') =
      BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st) := by
    refine (Asm.cmp_model X.mem qv (c.uuP j) (c.P s j U).length n' _ rfl).trans ?_
    rw [hlq, hlu]; rfl
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ hmcT ⟨?_, ?_, ?_⟩ ?_
  · show X.regs 30 = _; exact h30
  · show X.sp = _; exact hsp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h29
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [h1, h4, h0, h3, t0, t1, t3, t4]; exact hres
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s328
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s152
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hv4.s168
  · show m.readLE _ _ = _; rw [rw' _ _ (by omega)]; exact hsi

end FvModexp.Arm64.Q.DivRec
