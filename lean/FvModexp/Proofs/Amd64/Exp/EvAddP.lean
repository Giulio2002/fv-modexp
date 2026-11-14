import FvModexp.Proofs.Amd64.Exp.EvJ12
import FvModexp.Proofs.Amd64.Exp.EvMiP
import FvModexp.Proofs.Amd64.Exp.EvSm
import FvModexp.Proofs.Amd64.Exp.EvTrD

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `z.add(z, u)`'s precondition and frames (asm s64; twin of infra's arm64 `EvAddP`)

* `ZOK.gw` (a non-empty `ZOK` array is apart from the guard word and the TLS slot), `ZOK.sub`/`ZOK.subL` (the
  `stepC` destination obligations for `z`'s array), `LZ.rd` (`z` as an operand at `RSP = sp - 8`);
* `addPre0`: divmc's amd64 `NatAdd.Pre0` (window `4440 / 80`) at the callee entry (`RSP = sp - 8`) for `z.add(z, u)`:
  `z` = `(pZ, lw, cZ)` (an `LZ`; EMPTY `z` is the entry `z`, its window fact from the premise `hzw`), `u` a live local;
* `frm_dstZ`: `frm_dst` for a non-stack callee writing `z`'s array (`LZ` destination, possibly empty);
* `rs_zE`: `ResSep` for the entry `z`.
PERF (s63 lesson): no `omega` in the big contexts — arithmetic in the small lemmas `addK`, `mkc`, `mvk`, `zwin`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp

theorem tA {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem addK {K sp : Nat} (h : 42816 ≤ K ∧ K ≤ 2 ^ 20 ∧ K + 8 ≤ sp ∧ sp % 8 = 0 ∧ sp + 0x1b8 ≤ 2 ^ 48) :
    4440 ≤ K ∧ 4440 ≤ sp - 8 := by omega

theorem mkc {n : Nat} (h : n ≤ 2 ^ 13) : makeCap n ≤ 2 ^ 17 := by unfold makeCap; split <;> omega

theorem needA_le {lw lu : Nat} (hlw : lw ≤ 2 ^ 12) (hlu : lu ≤ 2 ^ 12) :
    (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ 2 ^ 13 := by split <;> omega

theorem mvk {lw lu k : Nat} (hlw : lw ≤ 2 ^ 12) (hlu : lu ≤ 2 ^ 12) (hk : k ≤ 8 * max lw lu) : k ≤ 2 ^ 20 := by
  omega

theorem lt40 {l c : Nat} (h1 : l ≤ c) (h2 : c < 2 ^ 40) : l < 2 ^ 40 := Nat.lt_of_le_of_lt h1 h2

theorem lt64 {c : Nat} (h2 : c < 2 ^ 40) : c < 2 ^ 64 := Nat.lt_trans h2 (by decide)

theorem mul8_le {a b : Nat} (h : a ≤ b) : 8 * a ≤ 8 * b := Nat.mul_le_mul_left 8 h

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a non-empty `ZOK` array is apart from the guard word and the TLS slot -/
theorem ZOK.gw (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {p c : Nat} (hc : 0 < c) (hz : ZOK R L st zp zc M L1 p c) :
    Apart p (8 * c) (g + 16) 8 ∧ Apart p (8 * c) (fs - 8) 8 := by
  have hce := hP.cenv0
  rcases hz with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · have h := hP.zF hc
    exact ⟨h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm⟩
  · exact ⟨(hin.apart hce.2.2.2.2.2.2.2.2.2.1).symm,
      (hin.apart hce.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm⟩

theorem ZOK.sub {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat} (h : ZOK R L st zp zc M L1 p c) :
    ∀ a n, Outside a n R.rt → Outside a n (ZS zp zc st s.mem) → Outside a n [(p, p + 8 * c)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
  · omega
  · have := hin.apart h1; unfold Apart at this; omega

theorem ZOK.subL {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat} (h : ZOK R L st zp zc M L1 p c) :
    ∀ a n, InRanges a n L → Outside a n (ZS zp zc st s.mem) → Outside a n [(p, p + 8 * c)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨-, hap, -⟩
  · omega
  · have := hap.apart_of_inRanges h1; omega

/-- `z` (non-empty) as a callee input at `RSP = sp - 8` -/
theorem LZ.rd (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {p l c v : Nat}
    (h : LZ R L st zp zc M L1 p l c v) (hl : 0 < l) {S : State}
    (hsp : (S.regs 4).toNat = sp - 8) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x7f) :
    EvenHyp.RdIn R L1 S stk above p l := by
  have hk := hP.kf
  obtain ⟨c40, hlv, hz, hlc, -, -⟩ := h
  have hc : 0 < c := Nat.lt_of_lt_of_le hl hlc
  obtain ⟨-, a2, a3, a4⟩ := hlv hc
  obtain ⟨-, w1, -, -⟩ := ZOK.ap hP hw hc (hz hc)
  unfold Apart at w1
  subst hm
  refine ⟨by omega, Janus.Arm64.Memory.accessible_weaken _
    (Janus.Arm64.Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega)), by omega, a2.sub (by omega) (by omega), ?_⟩
  simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

/-- `z`'s range (possibly EMPTY: then the entry `z`) outside the `add` window -/
theorem zwin (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hzw : Outside zp (8 * zc) [(sp - 8 - K, sp + 0x1b8)]) {pZ cZ : Nat}
    (hz : 0 < cZ → ZOK R L st zp zc M L1 pZ cZ) (hZe : cZ = 0 → pZ = zp ∧ cZ = zc)
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) : Outside pZ (8 * cZ) (win S' 4440 80) := by
  have hk := hP.kf
  simp only [win, tsp, outside_cons, outside_nil, and_true]
  rcases Nat.eq_zero_or_pos cZ with c0 | c0
  · obtain ⟨e1, e2⟩ := hZe c0
    rw [e1, e2]
    simp only [outside_cons, outside_nil, and_true] at hzw; omega
  · obtain ⟨-, w1, -, -⟩ := ZOK.ap hP hw c0 (hz c0)
    unfold Apart at w1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`nat.add`'s precondition** (`Pre0`) for `z.add(z, u)` at the callee entry `S'` (`RSP = sp - 8`) -/
theorem addPre0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hzw : Outside zp (8 * zc) [(sp - 8 - K, sp + 0x1b8)])
    {S' : State} (tsp : (S'.regs 4).toNat = sp - 8) (tg : (S'.regs 14).toNat = g) (tfs : S'.fsBase.toNat = fs)
    (fm : S'.mem = M)
    {pZ lw cZ vz pu lu cu vu : Nat} (hz : LZ R L st zp zc M L1 pZ lw cZ vz) (hZe : cZ = 0 → pZ = zp ∧ cZ = zc)
    (hZ64 : pZ < 2 ^ 64) (hu : LN R L s.mem st M L1 pu lu cu vu) (hu64 : pu < 2 ^ 64)
    (huz : 0 < cu → 0 < cZ → Apart pu (8 * cu) pZ (8 * cZ)) (hlw : lw ≤ 2 ^ 12) (hlu : lu ≤ 2 ^ 12)
    (hb : makeCost (if min lw lu = 0 then max lw lu else max lw lu + 1) ≤ b1) :
    NatAdd.Pre0 R b1 L1 (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 cZ) (BitVec.ofNat 64 pZ) (BitVec.ofNat 64 lw)
      (BitVec.ofNat 64 cZ) (BitVec.ofNat 64 pu) (BitVec.ofNat 64 lu) (BitVec.ofNat 64 cu) S' := by
  have hK := addK hP.kf
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2
  have hwT : Outside NatAdd.wordT 16 R.rt := by unfold NatAdd.wordT; exact hP.2.2.1
  have hce := CallW.callEnv_of (hw.cenv hP) tsp tg tfs fm (stk := 4440) (above := 80) hK.1 (by decide) hK.2
  have hcZ : cZ < 2 ^ 40 := hz.1
  have hcu : cu < 2 ^ 40 := hu.1.1
  have hlwc : lw ≤ cZ := hz.2.2.2.1
  have hluc : lu ≤ cu := hu.2.1
  have hzwin := zwin hP hw hzw hz.2.2.1 hZe tsp
  have hx : 0 < lw → M.accessible pZ (8 * lw) false = true ∧ pZ + 8 * lw ≤ 2 ^ 48 ∧ Held R L1 pZ (8 * lw) ∧
      Outside pZ (8 * lw) (win S' 4440 80) := fun hl => by
    have h := LZ.rd hP hw hz hl tsp fm (stk := 4440) (above := 80) hK.1 (by decide)
    exact ⟨by rw [← fm]; exact h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hy : 0 < lu → M.accessible pu (8 * lu) false = true ∧ pu + 8 * lu ≤ 2 ^ 48 ∧ Held R L1 pu (8 * lu) ∧
      Outside pu (8 * lu) (win S' 4440 80) := fun hl => by
    have h := LN.rd hP hu (Nat.lt_of_lt_of_le hl hluc) tsp fm (stk := 4440) (above := 80) hK.1 (by decide)
    exact ⟨by rw [← fm]; exact h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hgw : 0 < cZ → Apart pZ (8 * cZ) (g + 16) 8 ∧ Apart pZ (8 * cZ) (fs - 8) 8 := fun hc =>
    ZOK.gw hP hc (hz.2.2.1 hc)
  have hmk := mkc (needA_le hlw hlu)
  unfold NatAdd.Pre0
  simp only [NatAdd.need, NatAdd.mx]
  rw [tA hZ64, tA (lt64 hcZ), tA (lt64 (lt40 hlwc hcZ)), tA hu64, tA (lt64 (lt40 hluc hcu)),
    tA (lt64 hcu), tg, tfs, fm]
  refine ⟨hce, hwT, hlwc, hluc, hcZ, hcu, lt40 hlwc hcZ, lt40 hluc hcu, hcZ, hz.2.1, hzwin,
    fun hc => ⟨(hgw hc).1, (hgw hc).2, fun _ => Or.inl trivial,
      fun hl => Or.inr (apart_shrinkL (huz (Nat.lt_of_lt_of_le hl hluc) hc) (mul8_le hluc)).symm⟩, hx,
    hz.2.2.2.2.2, hu.2.2.2, hy, hw.inv,
    fun _ => ⟨hsv.1 _ _ _ hmk, hb⟩,
    fun d src k hk => hsv.2.1 d src k (mvk hlw hlu hk)⟩

set_option maxRecDepth 20000 in
/-- `frm_dst` for an `LZ` destination (`z`'s array; empty → the destination `(0, 0)`) -/
theorem frm_dstZ (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd ld cd vd : Nat}
    (hd : LZ R L st zp zc M L1 pd ld cd vd) {M' : Memory} {L2 : List (Nat × Nat)} (hx : LiveExt R L1 L2)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x7f)
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd)]))
    (hLF : LiveFrame M M' L1 [(pd, pd + 8 * cd)]) :
    ∃ qd kd : Nat, (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      Apart qd (8 * kd) (sp - 8 - K) (K + 0x1c0) ∧
      MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(qd, qd + 8 * kd)] ++ stkWs M st) ∧ StackBackL R L1 L2 st M M' ∧
      (stW M' st = stW M st ∧ stCap M' st = stCap M st) := by
  have hcw := hP.st_cw hstk habove
  rcases Nat.eq_zero_or_pos cd with c0 | c0
  · subst c0
    have hF0 := memFrame_drop_emptyE (by omega) hF
    have hL0 : LiveFrame M M' L1 [] :=
      liveFrame_drop_emptyE (ws := []) (p := pd) (e := pd + 8 * 0) (by omega)
        (by rw [List.nil_append]; exact hLF)
    have hF1 : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [((0 : Nat), 0 + 8 * 0)]) :=
      hF0.mono fun a n ho => by rw [outside_append] at ho; exact ho.1
    have hL1 : LiveFrame M M' L1 [((0 : Nat), 0 + 8 * 0)] :=
      Expmc.liveFrame_widen hL0 fun _ _ _ => by simp only [outside_nil]
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF1 hL1 hcw out_00
    exact ⟨0, 0, fun _ _ _ _ => out_00, fun _ _ _ _ => out_00, by unfold Apart; omega, f1, f2, f3, f4⟩
  · have hz := hd.2.2.1 c0
    obtain ⟨-, w1, w2, -⟩ := ZOK.ap hP h c0 hz
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF hLF hcw (out1_of_apart w2)
    exact ⟨pd, cd, ZOK.sub hz, ZOK.subL hz, w1, f1, f2, f3, f4⟩

/-- `ResSep` for the entry `z` -/
theorem rs_zE (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (hw : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ResSep s.mem M st zp zc := by
  intro hc hn
  rcases hw.kf with h | ⟨hin, hap⟩
  · exact absurd h hn
  · obtain ⟨⟨hzO1, -, -, -⟩, -⟩ := hP.zF hc
    rcases hzO1 with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart at this ⊢; omega
    · exact (hin.apart hO)

end

end FvModexp.Amd64.ExpEven
