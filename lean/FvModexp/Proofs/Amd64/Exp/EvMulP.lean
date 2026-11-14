import FvModexp.Proofs.Amd64.Exp.EvJ12
import FvModexp.Proofs.Amd64.Exp.EvMiP
import FvModexp.Proofs.Amd64.Exp.EvSm
import FvModexp.Proofs.Amd64.Exp.EvCall
import FvModexp.Proofs.Amd64.NatQ.MulHypQE

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `nat.mul`'s Q-form precondition and the call (asm s63; twin of infra's arm64 `EvMulP`/`EvDst`)

* `mulPre`: divmc's `Q.NatMul.MPre` (window `[sp - 8 - W, sp + 80)`, `W ≥ mulWX64`) at the callee entry (`RSP = sp - 8`)
  for a destination `z` (located, or EMPTY with `EL`), operands `x`, `y` (live locals, possibly empty).
* `stkPreA`: `Q.NatSqr.StkPre` at any `above ≤ 0x7f` (`miStk` generalised).
* `frmS_dst`: a stack callee's frame for a located or EMPTY destination (the empty range is dropped and replaced by `(0, 0)`).
* `mulCallE`: `Q.DivRec.MulHypQE` (on `ns ⊆ LibNE.names`) as a call in `LibNE` (continuation over `MPost`).
* `natOF_p64`: a result pointer below `2^64`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

theorem tNE {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem mul_aE : segAddr Extracted.program Q.NatMul.fn = 6228032 := by decide

theorem memFrame_drop_midE {m m' : Memory} {A B : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : MemFrame m m' (A ++ [(p, e)] ++ B)) : MemFrame m m' (A ++ B) :=
  ⟨fun a n ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      rw [outside_append] at ho
      have := h.readLE (a + i) 1 (by
        rw [outside_append, outside_append]
        refine ⟨⟨ho.1.of_sub (by omega) (by omega), ?_⟩, ho.2.of_sub (by omega) (by omega)⟩
        simp only [outside_cons, outside_nil, and_true]; omega)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm), h.accessible⟩

theorem liveFrame_drop_midE {m m' : Memory} {L B : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : LiveFrame m m' L ([(p, e)] ++ B)) : LiveFrame m m' L B :=
  ⟨fun a n hin ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := h.readLE (a + i) 1 ⟨r, hr, by omega, by omega⟩ (by
        rw [outside_append]
        refine ⟨?_, ho.of_sub (by omega) (by omega)⟩
        simp only [outside_cons, outside_nil, and_true]; omega)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm)⟩

/-- a result `(p', c')` of `MPost` form below `2^64` (the destination's pointer is, and a fresh result is non-empty) -/
theorem natOF_p64 {M : Memory} {R : RtInv} {L L' : List (Nat × Nat)} {zp zc need p' c' : Nat}
    (hor : (p' = zp ∧ c' = zc) ∨ (need ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hlv : NatLive M R L' p' c') (hzp : zp < 2 ^ 64) (hneed : 0 < need) : p' < 2 ^ 64 := by
  rcases hor with ⟨rfl, -⟩ | ⟨hn, -⟩
  · exact hzp
  · have := (hlv (by omega)).2.2.2; omega

/-- the window `[sp - 8 - W, sp + 80)` inside the frame -/
theorem win88_sub {S' : State} {sp K W : Nat} (tsp : (S'.regs 4).toNat = sp - 8) (hWK : W ≤ K) (hK8 : K ≤ sp - 8)
    {st : Nat} : ∀ a n, Outside a n [(sp - 8 - K, sp + 0x1b8), (st, st + 24)] → Outside a n (win S' W 88) :=
  fun a n ho => by simp only [win, tsp, outside_cons, outside_nil, and_true] at ho ⊢; omega

/-- an empty range apart from the frame is outside the window -/
theorem out_win0 {S' : State} {sp K W p : Nat} (tsp : (S'.regs 4).toNat = sp - 8) (hWK : W ≤ K)
    (h : Apart p (8 * 0) (sp - 8 - K) (K + 0x1c0)) : Outside p (8 * 0) (win S' W 88) := by
  simp only [win, tsp, outside_cons, outside_nil, and_true]; unfold Apart at h; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a stack callee's frame for a located or EMPTY destination -/
theorem frmS_dst (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {pd ld cd vd : Nat} (hd : LN R L s.mem st M L1 pd ld cd vd) {M' : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ ws ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) :
    ∃ qd kd : Nat, (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      Apart qd (8 * kd) (sp - 8 - K) (K + 0x1c0) ∧
      MemFrame M M' (R.rt ++ ws ++ [(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      (∀ q c, 0 < c → (0 < cd → Apart q (8 * c) pd (8 * cd)) → Apart q (8 * c) qd (8 * kd)) := by
  rcases Nat.eq_zero_or_pos cd with c0 | c0
  · subst c0
    have hF0 := memFrame_drop_midE (A := R.rt ++ ws) (by omega) hF
    have hL0 := liveFrame_drop_midE (by omega) hLF
    refine ⟨0, 0, fun _ _ _ _ => out_00, fun _ _ _ _ => out_00, by unfold Apart; omega,
      hF0.mono fun a n ho => ?_, Expmc.liveFrame_widen hL0 fun a n ho => ?_, fun _ _ _ _ => by unfold Apart; omega⟩
    · rw [outside_append, outside_append] at ho
      rw [outside_append]; exact ⟨ho.1.1, ho.2⟩
    · rw [outside_append] at ho; exact ho.2
  · have hloc := (hd.1.2.2 c0).1
    obtain ⟨w1, -, -, -⟩ := Loc.ap hP hloc
    exact ⟨pd, cd, Loc.sub hloc, Loc.subL hloc, w1, hF, hLF, fun _ _ hc h => h c0⟩

set_option maxRecDepth 20000 in
/-- **`StkPre`** at a callee entry `S'` (`RSP = sp - 8`, window `[sp - 8 - W, sp - 8 + A)`, `W ≤ K`, `A ≤ 0x7f`) -/
theorem stkPreA (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S' : State} (tsp : (S'.regs 4).toNat = sp - 8)
    (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs) (fm : S'.mem = M) {W A : Nat} (hW : W ≤ K)
    (hA : A ≤ 0x7f) : StkPre R L1 S' W A st := by
  have hk := hP.kf
  obtain ⟨hst0, -, hok, -, -, -, -, hc0, -, hstwb, hstf, hfgA, hftl⟩ := nstk_of hP h (KN := 0) (by omega)
  obtain ⟨hstw, hstg, hsttl, -, -, -, -⟩ := hP.stkF
  have har := arr_at hP h
  have hogA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlc := hok.2.2.2.2.2.1
  have hnl := hok.2.2.2.2.1
  subst fm
  simp only [StkPre, Q.BasicSqr.freeP, Q.BasicSqr.freeN, Q.NatSqr.guard, Q.NatSqr.tls, win, tsp, tg, tfs]
  simp only at hstf hfgA hftl
  unfold Apart at hstw
  refine ⟨by omega, hok, by simp only [outside_cons, outside_nil, and_true]; omega, hstg, fun hc => ?_, ?_, ?_,
    hstf, hstwb, ?_, (hogA.2.2.1).symm, hfgA, hsttl, fun hc => (har hc).2.2, hftl⟩
  · obtain ⟨a1, a2, -⟩ := har hc
    unfold Apart at a1
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, a2⟩
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [hc0 e, e]; unfold Apart; omega
    · have := (har e).2.1; unfold Apart at this ⊢; omega
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · simp only [outside_cons, outside_nil, and_true]; rw [hc0 e, e]; omega
    · have := (har e).1; unfold Apart at this
      simp only [outside_cons, outside_nil, and_true]; omega
  · rcases Nat.eq_zero_or_pos (stCap S'.mem st) with e | e
    · rw [hc0 e, e, show stLen S'.mem st = 0 by omega]; exact Or.inr outside_zero
    · exact (hnl e).2.1.sub (by omega) (by omega)

/-- an operand's `Ops` part (`x` or `y`) -/
theorem opPart (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {S' : State} (tsp : (S'.regs 4).toNat = sp - 8)
    (fm : S'.mem = M) {W : Nat} (hWK : W ≤ K) {p l c v : Nat} (hq : LN R L s.mem st M L1 p l c v)
    (hl : l ≤ 2 ^ 12) :
    l ≤ c ∧ c < 2 ^ 40 ∧ l ≤ 2 ^ 12 ∧ (0 < l → S'.mem.accessible p (8 * l) false = true) ∧
      (0 < c → Held R L1 p (8 * c) ∧ p + 8 * c ≤ 2 ^ 48) ∧
      (0 < l → Outside p (8 * l) (win S' W 88) ∧ StkSep S'.mem st p (8 * l)) := by
  refine ⟨hq.2.1, hq.1.1, hl, fun h0 => ?_, fun h0 => ⟨((hq.1.2.1 h0)).2.1, (hq.1.2.1 h0).2.2.2⟩, fun h0 => ?_⟩
  · exact (LN.rd hP hq (Nat.lt_of_lt_of_le h0 hq.2.1) tsp fm (stk := W) (above := 88) hWK (by decide)).2.1
  · have hc : 0 < c := Nat.lt_of_lt_of_le h0 hq.2.1
    refine ⟨(LN.rd hP hq hc tsp fm (stk := W) (above := 88) hWK (by decide)).2.2.2.2, ?_⟩
    rw [fm]; exact miOp hP hw hq hc (Nat.mul_le_mul_left 8 hq.2.1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.mul`'s Q-form precondition** at the callee entry `S'` (`RSP = sp - 8`) -/
theorem mulPre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {W : Nat} (hWK : W ≤ K)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M) {pd ld cd vd px lx cx vx py ly cy vy : Nat}
    (hd : LN R L s.mem st M L1 pd ld cd vd) (hde : EL R L pd cd)
    (hx : LN R L s.mem st M L1 px lx cx vx) (hy : LN R L s.mem st M L1 py ly cy vy)
    (hdx : 0 < cx → 0 < cd → Apart px (8 * cx) pd (8 * cd)) (hdy : 0 < cy → 0 < cd → Apart py (8 * cy) pd (8 * cd))
    (hlx : lx ≤ 2 ^ 12) (hly : ly ≤ 2 ^ 12) (hmW : mulW64 lx ly ≤ W) (hs16 : ℓ + 4 * (lx + ly) + 64 ≤ 2 ^ 16) {H : Nat}
    (hH : ℓ + 4 * (lx + ly) + 64 ≤ H) (hb : mulCQ lx ly + stkR H M st ≤ b1) :
    Q.NatMul.MPre R b1 H L1 W pd cd st px lx cx py ly cy S' := by
  have hk := hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.1
  have hadx : M.accessible Callees.adxAddr 1 false = true := by rw [hw.fr.accessible]; exact hP.2.2.2.1
  have hK8 : K ≤ sp - 8 := Nat.le_sub_of_add_le hk.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := W) (above := 88) hWK (by decide)
    (Nat.le_trans hWK hK8)
  have hgl := hw.globals hP (w := win S' W 88) (win88_sub tsp hWK hK8)
  have hox := opPart hP hw tsp fm hWK hx hlx
  have hoy := opPart hP hw tsp fm hWK hy hly
  have hwr := DL.wr hP hd.1 tsp tg tfs fm (stk := W) (above := 88) hWK (by decide)
  have hdw : Outside pd (8 * cd) (win S' W 88) := by
    rcases Nat.eq_zero_or_pos cd with c0 | c0
    · subst c0
      exact out_win0 tsp hWK (EL.out hde hP.win_rt)
    · exact (hwr.2.2 c0).1
  have hsk := stkPreA hP hw tsp tg tfs fm (W := W) (A := 88) hWK (by decide)
  have hlen : stLen S'.mem st = ℓ := by rw [fm]; exact hw.len
  have hzs : 0 < cd → Apart pd (8 * cd) ((S'.regs 14).toNat + 16) 8 ∧ Apart pd (8 * cd) (Q.NatSqr.tls S') 8 ∧
      StkSep S'.mem st pd (8 * cd) := fun c0 =>
    ⟨(hwr.2.2 c0).2.1, (hwr.2.2 c0).2.2, by rw [fm]; exact miOp hP hw hd c0 (Nat.le_refl _)⟩
  have hax : (pd = px ∧ cd = cx) ∨ (0 < cd → 0 < lx → Apart pd (8 * cd) px (8 * lx)) :=
    Or.inr fun hc hl => apart_shrink (hdx (Nat.lt_of_lt_of_le hl hx.2.1) hc).symm (Nat.mul_le_mul_left 8 hx.2.1)
  have hay : (pd = py ∧ cd = cy) ∨ (0 < cd → 0 < ly → Apart pd (8 * cd) py (8 * ly)) :=
    Or.inr fun hc hl => apart_shrink (hdy (Nat.lt_of_lt_of_le hl hy.2.1) hc).symm (Nat.mul_le_mul_left 8 hy.2.1)
  refine ⟨hce, hmW, hsv, by rw [fm]; exact hgl, hwT, ⟨hox, hoy, ⟨hd.1.1, by rw [fm]; exact hd.1.2.1, hdw, hzs, hax, hay⟩,
    by rw [hlen]; exact hs16⟩, hsk, ⟨by rw [hlen]; exact hH, by rw [fm]; exact hb⟩, by rw [fm]; exact hadx,
    by rw [tg, fm]; exact hw.inv⟩

end

set_option maxRecDepth 20000 in
/-- a call of the Q-form `nat.mul` (`MulHypQE` on `ns ⊆ LibNE.names`) from its entry -/
theorem mulCallE {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) {W : Nat}
    (hml : Q.DivRec.MulHypQE impl R ns W) (H : Nat) {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st xp xl xc yp yl yc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6228032) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64)
    (hy0 : S.mem.readLE ((S.regs 4).toNat + 8) 8 = yp) (hy1 : S.mem.readLE ((S.regs 4).toNat + 16) 8 = yl)
    (hy2 : S.mem.readLE ((S.regs 4).toNat + 24) 8 = yc)
    (hpre : Q.NatMul.MPre R b H L W zp zc st xp xl xc yp yl yc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Q.NatMul.MPost R b H L W zp zc st xp xl xc yp yl yc S s' → ReachesRet (LibNE.program.link impl) ret s' Qp) :
    ReachesRet (LibNE.program.link impl) ret S Qp := by
  have hS := Ensures.toSummaryIn (hml H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) yp yl yc)
    (A64.noExit_restrict64 hap ns) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap hns)
  rw [mul_aE] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp only [ArgsFrom64, argReg, intArgRegs]; exact ⟨h0, h3, h1, h7, h6, h8, h9, trivial⟩
  · rw [tNE bz, tNE bzc, tNE bst, tNE bx, tNE bxl, tNE bxc]
    exact ⟨hy0, hy1, hy2, hpre⟩
  · rw [tNE bz, tNE bzc, tNE bst, tNE bx, tNE bxl, tNE bxc] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

end FvModexp.Amd64.ExpEven
