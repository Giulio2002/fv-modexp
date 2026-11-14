import FvModexp.Proofs.Amd64.Exp.EvSmP
import FvModexp.Proofs.Amd64.Exp.EvSmR

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the `subMod2N` call's result facts (asm s62; twin of infra's arm64 `EvSm`)

`LN.of_sm`: a `PostG`-style result (the destination `z1`'s array or fresh) is a live local. `apart_res`: its apartness
from a range held at the call. `frm_dst`: the callee frame in the `stepC` form for a located or EMPTY destination
(the empty range is dropped and replaced by `(0, 0)`). `kk_push2`: the keep range through `runSm`'s writes
`[sp - 8, sp + 8)` (push + stack argument `n`). The run itself is `runSm` (EvSmR).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- adapted from infra's amd64 `SubMod2N.memFrame_drop_empty` (Amd64/Exp/SubMod2NGL.lean; kept local so the Even
chain does not import the subMod2N proof chain) -/
theorem memFrame_drop_emptyE {m m' : Memory} {rs : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : MemFrame m m' (rs ++ [(p, e)])) : MemFrame m m' rs :=
  ⟨fun a n ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      have := h.readLE (a + i) 1 (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨ho.of_sub (by omega) (by omega), by omega⟩)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm), h.accessible⟩

/-- adapted from infra's amd64 `SubMod2N.liveFrame_drop_empty` (Amd64/Exp/SubMod2NGL.lean) -/
theorem liveFrame_drop_emptyE {m m' : Memory} {L ws : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : LiveFrame m m' L (ws ++ [(p, e)])) : LiveFrame m m' L ws :=
  ⟨fun a n hin ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := h.readLE (a + i) 1 ⟨r, hr, by omega, by omega⟩ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨ho.of_sub (by omega) (by omega), by omega⟩)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm)⟩

theorem sm_a : segAddr Extracted.program SubMod2N.fn = smE := by decide

/-- the keep range through the push + one stack-argument word and a callee with `above ≤ 0x7f` -/
theorem kk_push2 {sp : Nat} {M0 M M' : Memory} {ab : Nat} (hsp : 8 ≤ sp) (hab : ab ≤ 0x7f)
    (hF : MemFrame M0 M [(sp - 8, sp + 8)])
    (hkc : ∀ a k, sp - 8 + ab ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) :
    ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k := fun a k h1 h2 => by
  rw [hkc a k (by omega) h2, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]

theorem natVal_lt64 (m : Memory) (p l : Nat) : natVal m p l < 2 ^ (64 * l) := by
  have := Janus.Arm64.Memory.readLE_lt m p (8 * l)
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * l) = 64 * l by omega] at this
  exact this

/-- a value below `2^(64 ml)` (`ml ≤ 128`) has at most `2^12` limbs -/
theorem len_bdE {M : Memory} {p l ml v : Nat} (hN : NatNorm M p l) (hv : natVal M p l = v) (hlt : v < 2 ^ (64 * ml))
    (hml : ml ≤ 128) : l ≤ 2 ^ 12 := by
  have := nlen_bd' hN (by rw [hv]; exact hlt); omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a callee result in the destination's array or fresh (`subMod2N`'s `PostG` form) is a live local nat -/
theorem LN.of_sm (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd ld cd vd : Nat}
    (hd : LN R L s.mem st M L1 pd ld cd vd) {M' : Memory} {L2 : List (Nat × Nat)} {p' l' c' v : Nat}
    (hv : natVal M' p' l' = v) (hn : NatNorm M' p' l') (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40)
    (hlv : NatLive M' R L2 p' c')
    (hor : (p' = pd ∧ c' = cd) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1))
    (hx : LiveExt R L1 L2) (hsb : StackBackL R L1 L2 st M M') (hrs : ResSep M M' st p' c') :
    LN R L s.mem st M' L2 p' l' c' v := by
  refine ⟨⟨hc40, hlv, fun hc => ?_⟩, hlc, hv, hn⟩
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · obtain ⟨l1, o1⟩ := hd.1.2.2 hc
    exact ⟨l1, o1.back hx hsb.1⟩
  · exact ⟨Or.inr ⟨hin, fun r hr => hap r (h.le.mem_old hr)⟩,
      ob_fresh h.sok (WC.cap0 hP h) hin hap (hlv hc).2.1 hrs hc⟩

end

/-- the result's apartness from a range held at the call -/
theorem apart_res {R : RtInv} {L1 : List (Nat × Nat)} {pd cd p' c' q k : Nat}
    (hor : (p' = pd ∧ c' = cd) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1))
    (hh : Held R L1 q k) (hre : 0 < cd → Apart pd (8 * cd) q k) : 0 < c' → Apart p' (8 * c') q k := by
  intro hc
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · exact hre hc
  · exact hfresh hh hap hin

theorem out_00 {a k : Nat} : Outside a k [((0 : Nat), 0 + 8 * 0)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the frames of a non-stack callee writing its window and `[pd, pd + 8 cd)` in the `stepC` form, for a located
destination (`0 < cd`) or an EMPTY one (then as the destination `(0, 0)`) -/
theorem frm_dst (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd ld cd vd : Nat}
    (hd : LN R L s.mem st M L1 pd ld cd vd) {M' : Memory} {L2 : List (Nat × Nat)} (hx : LiveExt R L1 L2)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x7f)
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd)]))
    (hLF : LiveFrame M M' L1 [(pd, pd + 8 * cd)]) :
    ∃ qd kd : Nat, (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      Apart qd (8 * kd) (sp - 8 - K) (K + 0x1c0) ∧
      MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(qd, qd + 8 * kd)] ++ stkWs M st) ∧ StackBackL R L1 L2 st M M' ∧
      (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∧
      (∀ q c, 0 < c → (0 < cd → Apart q (8 * c) pd (8 * cd)) → Apart q (8 * c) qd (8 * kd)) := by
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
    exact ⟨0, 0, fun _ _ _ _ => out_00, fun _ _ _ _ => out_00, by unfold Apart; omega, f1, f2, f3, f4,
      fun _ _ _ _ => by unfold Apart; omega⟩
  · have hloc := (hd.1.2.2 c0).1
    obtain ⟨w1, w2, -, -⟩ := Loc.ap hP hloc
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF hLF hcw (out1_of_apart w2)
    exact ⟨pd, cd, Loc.sub hloc, Loc.subL hloc, w1, f1, f2, f3, f4, fun _ _ hc h => h c0⟩

end

end FvModexp.Amd64.ExpEven
