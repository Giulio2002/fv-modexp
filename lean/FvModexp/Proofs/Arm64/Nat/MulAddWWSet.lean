import FvModexp.Proofs.Arm64.Nat.MulAddWWMid

/-!
# `nat.mulAddWW` (arm64): `m == 0 || y == 0` → `return z.setWord(r)` (`+0xc0` … return)

At `+0xc0` (after the frame push and the spills `R0 → SP + 8`, `R3 → SP + 32`, `R7 → SP + 64`): `CBNZ R7`;
`r = 0`: `R1 = 0`, return `z[:0]` (`setZero`); `r ≠ 0`, `zc ≠ 0`: `z[0] = r`, return `z[:1]` (`setReuse`);
`r ≠ 0`, `zc = 0`: `makeslice(Word, 1, 1)`, `ptr[0] = r` (reloaded from `SP + 64`), return `(ptr, 1, 1)` (`setAlloc`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.MulAddWW

abbrev hSet : Nat := segAddr Extracted.program fn + 0xc0

/-- The boundary facts at `+0xc0`. -/
structure SetRel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s : State)
    (M : Memory) : Prop where
  pre : Pre R b L zp zc xp xl y r s
  xy : natVal s.mem xp.toNat xl.toNat * y.toNat = 0
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  hF : MemFrame s.mem M (winA s 4208 72)
  r1 : M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat
  r2 : M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat
  r3 : M.readLE (s.sp.toNat + 64) 8 = r.toNat
  hd : Extracted.program.DataLoaded M

theorem SetRel.need {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y r : BitVec 64} {s : State}
    {M : Memory} (h : SetRel R b L zp zc xp xl y r s M) (hxy : xl.toNat = 0 ∨ y.toNat = 0) :
    need xl y r = if r.toNat = 0 then 0 else 1 := by
  unfold MulAddWW.need; rw [if_pos hxy]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setZero (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (M : Memory) (h : SetRel R b L zp zc xp xl y r s M) (hr : r.toNat = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = zp) (h2 : S.regs 2 = zc) (h7 : S.regs 7 = r)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, hx40, hz40, hzl, -, -, -, -, -, -,
    hinv, -⟩, hxy, hl4, hl48, hF, r1, r2, r3, -⟩ := h
  have hr0 : r = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr)
  subst hr0
  janus_run [hm, r1, r2]
  refine ⟨zp.toNat, 0, zc.toNat, ?_, ?_, ?_, by simp [hxy], Or.inl rfl, by omega, by omega, L, b, LiveExt.refl R L,
    Nat.sub_le _ _, inv_frame_winA hF hout hb' (by omega) hinv, fun hc => ?nl, Or.inl ⟨rfl, rfl⟩,
    MemFrame.mono hF fun a n h => by simp only [outside_append] at h; exact h.1.2,
    liveFrame_of_frame (rs := winA s 4208 72) (MemFrame.mono hF fun a n h => by
        simp only [outside_append] at h; exact h.1)
      (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)⟩
  case nl =>
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by rw [hF.accessible]; exact hzacc, hz48⟩
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setReuse (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (M : Memory) (h : SetRel R b L zp zc xp xl y r s M) (hr : r.toNat ≠ 0) (hzc : zc.toNat ≠ 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = zp) (h2 : S.regs 2 = zc) (h7 : S.regs 7 = r)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, hx40, hz40, hzl, hzw', -, -, -, -, -,
    hinv, -⟩, hxy, hl4, hl48, hF, r1, r2, r3, -⟩ := h
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hr0 : (r = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hr; rw [e]; rfl
  have hz0 : (zc = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hzc; rw [e]; rfl
  have hzacc' : M.accessible zp.toNat (8 * zc.toNat) true = true := by rw [hF.accessible]; exact hzacc
  have hz8 : M.accessible zp.toNat 8 true = true := Memory.accessible_mono _ hzacc' (Nat.le_refl _) (by omega)
  janus_run [hm, r1, r2, hr0, hz0]
  have hin : InRanges zp.toNat 8 (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) :=
    ⟨(zp.toNat, zp.toNat + 8 * zc.toNat), by simp, Nat.le_refl _, by simp only; omega⟩
  have hmf : MemFrame s.mem M (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) :=
    MemFrame.mono hF fun a n h => by simp only [outside_append] at h; exact h.1.2
  have hlf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)] :=
    liveFrame_of_frame (rs := winA s 4208 72) (MemFrame.mono hF fun a n h => by
        simp only [outside_append] at h; exact h.1)
      (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)
  refine ⟨zp.toNat, 1, zc.toNat, ?_, ?_, ?_, ?_, Or.inr ?_, by omega, by omega, L, b, LiveExt.refl R L,
    Nat.sub_le _ _, ?_, fun _ => ⟨hzal, hzh, ?_, hz48⟩, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  all_goals try janus_simp
  · rw [hxy]; omega
  · exact hr
  · exact inv_store_held (inv_frame_winA hF hout hb' (by omega) hinv) (hzh.sub (Nat.le_refl _) (by omega))
  · exact hzacc
  · exact hmf.writeLE_inRanges _ hin
  · exact LiveFrame.writeLE_ws hlf _ ⟨(zp.toNat, zp.toNat + 8 * zc.toNat), by simp, Nat.le_refl _, by simp only; omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setAlloc (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (M : Memory) (h : SetRel R b L zp zc xp xl y r s M) (hxy0 : xl.toNat = 0 ∨ y.toNat = 0)
    (hr : r.toNat ≠ 0) (hzc : zc.toNat = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = zp) (h2 : S.regs 2 = zc) (h7 : S.regs 7 = r)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  have hneed := h.need hxy0
  rw [if_neg hr] at hneed
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, hro⟩, hty, hx40, hz40, -, -, -, -, -, -,
    -, hinv, hok⟩, hxy, hl4, hl48, hF, r1, r2, r3, hd⟩ := h
  rw [hneed] at hok
  obtain ⟨hok1, hcost⟩ := hok (by omega)
  rw [show makeCap 1 = 1 by rfl] at hok1
  have hmc : makeCost 1 = allocCost 8 := rfl
  have hbl := blockSize_le_allocCost 8 true
  have hbs : blockSize 8 true ≤ b := by omega
  have hwM : M.accessible (s.sp.toNat - 4208) (4208 + 72) true = true := by rw [hF.accessible]; exact hw
  have hgM : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    unfold Apart at hga
    exact hF.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hgaM : M.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hF.accessible]; exact hg2
  have hinvM : R.inv b L (s.regs 28).toNat (view R.rt L M) := inv_frame_winA hF hout hb' (by omega) hinv
  have hwt : Apart wordT 16 (s.sp.toNat - 4208) (4208 + 72) := apart_of_data hd 1 (by decide) (by decide) hwM
  unfold Apart at hwt hga
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt
  simp only [LiveSep, win] at hLs
  have hr0 : (r = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hr; rw [e]; rfl
  have hz0 : zc = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hzc)
  subst hz0
  clear hinv hw hg2
  janus_run [hm, r1, r2, r3, hr0, hgM] calls [hmk.pos]
  rename_i P _ _ _ m1 _ _ hLF hMF hApL hInR hle hacc h8 _ _ _ hrb hinv' hwa hga' hta
  have hext : LiveExt R L (L ++ [(P.toNat, P.toNat + 8)]) := LiveExt.single (by simpa using hInR) (by simpa using hApL)
  have hPin : InRanges P.toNat 8 (L ++ [(P.toNat, P.toNat + 8)]) :=
    ⟨(P.toNat, P.toNat + 8), by simp, Nat.le_refl _, by simp only; omega⟩
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * (0#64).toNat)]) →
      Outside a n (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  have hmf1 : MemFrame s.mem m1 (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * (0#64).toNat)]) :=
    (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, hmo a n h⟩
  have hlf1 : LiveFrame s.mem m1 L [(zp.toNat, zp.toNat + 8 * (0#64).toNat)] := by
    refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n hin trivial]
    refine hF.readLE a n ?_
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq; simp only [outside_cons, outside_nil, and_true] at this
    simp only [winA, outside_cons, outside_nil, and_true]; omega
  obtain ⟨q, hq, hq1, hq2⟩ := hInR
  refine ⟨P.toNat, 1, 1, ?_, ?_, ?_, ?val, Or.inr ?nn, by omega, by omega, L ++ [(P.toNat, P.toNat + 8)], b - 8,
    hext, ?bud, inv_store_held hinv' (Or.inl hPin), fun _ => ⟨h8, Or.inl ?held, ?acc1, by omega⟩,
    Or.inr ⟨⟨q, hq, hq1, by omega⟩, fun r hr => (hApL r hr).mono (by omega) (Nat.le_refl _)⟩,
    hmf1.writeLE_inRanges _ ⟨q, by simp [hq], hq1, hq2⟩, LiveFrame.writeLE hlf1 _ (ApartAll.outside hApL)⟩
  case bud => rw [hneed, hmc]; unfold allocCost; omega
  case held => exact ⟨(P.toNat, P.toNat + 8), by simp, Nat.le_refl _, by simp only; omega⟩
  all_goals try janus_simp
  case val => rw [hxy]; omega
  case nn => exact hr
  case acc1 => exact hacc

end FvModexp.Arm64.MulAddWW
