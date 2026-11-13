import FvModexp.Proofs.Amd64.NatQ.DivLargeMem
import FvModexp.Proofs.Amd64.NatQ.DivLargePro

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeMemN.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `Mem` after `v := stk.nat(n)` (`mem_of_nat`) — pure

Twin of the arm64 `DivLargeMem.mem_of_nat`. `slotsW s`: the frame slots a segment between `stk.nat`'s return and the
division call may write (the window minus `Mem`'s preserved slots: `dbit` at `-209`, `vtop` at `-168`, `il + 1`/`m` at
`-136 … -120`, the defer record and `BP` at `-40 … 0`, the return address and the caller's area `0 … +112`); the scratch
`v` header slots `-96`, `-160`, `-152` are inside `slotsW` and given by value (`r1 r2 r3`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

/-- the frame slots written between `stk.nat`'s return and the division call besides `Mem`'s (see the module doc) -/
@[reducible] def slotsW (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 41272, (s.regs 4).toNat - 209), ((s.regs 4).toNat - 208, (s.regs 4).toNat - 168),
    ((s.regs 4).toNat - 160, (s.regs 4).toNat - 136), ((s.regs 4).toNat - 120, (s.regs 4).toNat - 40)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`Mem` after `stk.nat`** (pure): from the prologue facts (`AtNat`), `stk.nat`'s frame (`AfterNat`), and a frame `hM`
of the slots written since (and of a runtime call: `R.rt` with a `LiveFrame`). -/
theorem mem_of_nat {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {P S2 : State}
    (hP : AtNat st up uc il vp vl zp zc s P) (hA : AfterNat R b H L st vl s P S2 L1 b1)
    (hw1 : S2.mem.readLE st 8 = w1) (hl1 : S2.mem.readLE (st + 8) 8 = stLen s.mem st + StackNat.rnd vl)
    (hc1 : S2.mem.readLE (st + 16) 8 = c1)
    {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat} (hM : MemFrame S2.mem M (R.rt ++ slotsW s))
    (hML : LiveFrame S2.mem M L1 [])
    (r1 : M.readLE ((s.regs 4).toNat - 96) 8 = t) (r2 : M.readLE ((s.regs 4).toNat - 160) 8 = vl)
    (r3 : M.readLE ((s.regs 4).toNat - 152) 8 = vl) (hinv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk M)) :
    Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk M := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hsw := hl.sw
  have hpre := hE.pre
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hpre.ce.2.2.2.2.1
  obtain ⟨⟨-, -, htg⟩, htr, htw⟩ := hpre.ce.2.2.2.2.2.2.2.2.2
  unfold Apart at htw
  have hstt := hpre.stt; unfold Apart at hstt
  have hft := hpre.stft; unfold Apart at hft
  have hstarr := hpre.sti.2.2.2
  -- a window range apart from the stack's written ranges
  have wS : ∀ a n, (s.regs 4).toNat - 41272 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → Outside a n (stkWs s.mem st) := by
    intro a n h1 h2
    refine outside_stkWs hpre (by unfold Apart; omega) fun hc => ?_
    have := (hstarr hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; unfold Apart; omega
  -- `M` = `P.mem` on a window range outside the callee area and `slotsW`
  have rdP : ∀ a n, (s.regs 4).toNat - 41272 ≤ a → a + n ≤ (s.regs 4).toNat + 112 →
      (a + n ≤ (s.regs 4).toNat - 4504 ∨ (s.regs 4).toNat - 288 ≤ a) → Outside a n (slotsW s) →
      M.readLE a n = P.mem.readLE a n := by
    intro a n h1 h2 h3 h5
    rw [hM.readLE a n (by rw [outside_append]; exact ⟨hout.of_sub h1 (by omega), h5⟩),
      hA.F2.readLE a n (by
        rw [outside_append, outside_append]
        exact ⟨⟨hout.of_sub h1 (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩, wS a n h1 h2⟩),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have so : ∀ a n, ((s.regs 4).toNat - 209 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 208) ∨
      ((s.regs 4).toNat - 168 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 160) ∨
      ((s.regs 4).toNat - 136 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 120) ∨
      ((s.regs 4).toNat - 40 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 112) → Outside a n (slotsW s) := by
    intro a n h; simp only [slotsW, outside_cons, outside_nil, and_true]; omega
  have k : ∀ (a : Nat) {x : Nat}, (s.regs 4).toNat - 41272 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 →
      (a + 8 ≤ (s.regs 4).toNat - 4504 ∨ (s.regs 4).toNat - 288 ≤ a) → Outside a 8 (slotsW s) →
      P.mem.readLE a 8 = x → M.readLE a 8 = x :=
    fun a _ h1 h2 h3 h5 hx => (rdP a 8 h1 h2 h3 h5).trans hx
  -- `M` = `s.mem` on a stack argument slot / the return address
  have kS : ∀ (a : Nat) {x : Nat}, (s.regs 4).toNat ≤ a → a + 8 ≤ (s.regs 4).toNat + 56 →
      s.mem.readLE a 8 = x → M.readLE a 8 = x := by
    intro a _ h1 h2 hx
    rw [rdP a 8 (by omega) (by omega) (by omega) (so _ _ (by omega)), hP.fr.readLE a 8 (by
      simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
    exact hx
  -- `M` = `S2.mem` on a range held in `L` outside the window
  have hS2 : ∀ a n, Held R L a n → (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      M.readLE a n = S2.mem.readLE a n := by
    intro a n hh hw
    rcases hh with hi | ho
    · exact hML.readLE a n (hE.ext.inRanges_old hi) (by simp)
    · exact hM.readLE a n (by
        rw [outside_append]; exact ⟨ho, by simp only [slotsW, outside_cons, outside_nil, and_true]; omega⟩)
  have hsth : Held R L st 24 := hpre.sti.1.2.1
  refine {
    ra := kS _ (by omega) (by omega) rfl,
    bp := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.bp,
    dbit := by rw [rdP _ _ (by omega) (by omega) (by omega) (so _ _ (by omega))]; exact hP.dbit,
    vtop := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.vtop,
    il1 := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.il1,
    mm := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.mm,
    vt := r1, vn1 := r2, vn2 := r3,
    dfn := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.dfn,
    dst := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.dst,
    dn := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.dn,
    dp := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.dp,
    ipS := kS _ (by omega) (by omega) hpre.ipS,
    ilS := kS _ (by omega) (by omega) hpre.ilS,
    vpS := kS _ (by omega) (by omega) hpre.vpS,
    vlS := kS _ (by omega) (by omega) hpre.vlS,
    s1 := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.s1,
    s3 := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.s3,
    s4 := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.s4,
    s5 := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.s5,
    s7 := k _ (by omega) (by omega) (by omega) (so _ _ (by omega)) hP.s7,
    hw := by rw [hS2 _ _ (hsth.sub (Nat.le_refl _) (by omega)) (by omega)]; exact hw1,
    hlen := by rw [hS2 _ _ (hsth.sub (by omega) (by omega)) (by omega)]; exact hl1,
    hcap := by rw [hS2 _ _ (hsth.sub (by omega) (by omega)) (by omega)]; exact hc1,
    tls := ?tls, vs := ?vs, fr := ?fr, lf := ?lf, inv := hinv }
  case tls =>
    rw [hM.readLE _ _ (by
        rw [outside_append]; exact ⟨htr, by simp only [slotsW, outside_cons, outside_nil, and_true]; omega⟩),
      hA.F2.readLE _ _ (by
        simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨htr, by omega⟩, by omega, by omega⟩),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hP.fr.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
    exact htg
  case vs =>
    intro a n h1 h2
    have hvh : Held R L a n := hpre.vo.2.2.2.1.sub h1 h2
    have hvw := hl.vw
    have hsv := hpre.svv
    unfold Apart at hsv
    have hstk : Outside a n (stkWs s.mem st) := by
      simp only [stkWs, outside_cons, outside_nil, and_true]; omega
    rw [hS2 a n hvh (by omega)]
    have e : S2.mem.readLE a n = (P.mem.writeLE ((s.regs 4).toNat - 312) 8 raNat).readLE a n := by
      rcases hvh with hi | ho
      · exact hA.LF2.readLE a n hi hstk
      · exact hA.F2.readLE a n (by
          rw [outside_append, outside_append]
          exact ⟨⟨ho, by simp only [outside_cons, outside_nil, and_true]; omega⟩, hstk⟩)
    rw [e, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hP.fr.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)]
  case fr =>
    have hW : MemFrame P.mem (P.mem.writeLE ((s.regs 4).toNat - 312) 8 raNat)
        [((s.regs 4).toNat - 312, (s.regs 4).toNat - 304)] :=
      ⟨fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h
        exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
       fun a n v => by simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
    refine (mfTrans hP.fr (mfTrans hW (mfTrans hA.F2 hM))).mono fun a n ho => ?_
    simp only [win, stkWs, wsL, proWs, slotsW, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    obtain ⟨hrt, hwin, -, -, -, h5, h6⟩ := ho
    exact ⟨by omega, by omega, by omega, hrt, by omega, h5, h6, hrt, by omega, by omega, by omega, by omega⟩
  case lf =>
    refine ⟨fun a n hin hws => ?_⟩
    have hw0 : a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r (hE.ext.mem_old hr); omega
    have hws' : Outside a n (stkWs s.mem st) := by rw [outside_append] at hws; exact hws.2
    rw [hML.readLE a n (hE.ext.inRanges_old hin) (by simp), hA.LF2.readLE a n hin hws',
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hP.fr.readLE a n (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)

end FvModexp.Amd64.Q.DivLarge
