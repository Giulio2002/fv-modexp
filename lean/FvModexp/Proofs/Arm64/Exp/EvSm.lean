import FvModexp.Proofs.Arm64.Exp.EvSmP
import FvModexp.Proofs.Arm64.Exp.EvCalls
import FvModexp.Proofs.Arm64.Exp.LibCalls
import FvModexp.Proofs.Arm64.Exp.SubMod2NGL

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `mvJ` → `z1 = z1.subMod2N(z1, z2, n)` → `smR` (agent infra)

`runSm`: the argument moves (`z1` from the slots `264/152/160` twice, `z2` from `X0/X4/X2`, `n` from `184`) and the
call. `segSm` (`J9 → J10`): premise `SubMod2N.EnsG` (infra's general summary: any `cap z1`, empty `z1` / `z2`), `PreG`
from `smPre`; a non-stack callee (`nonStk`); the destination `z1`'s array, or (EMPTY `z1`) nothing: the empty range is
dropped from the frames (`memFrame_drop_empty`) and the step uses the trivially apart destination `(0, 0)`.
The result is located (`LN.of_sm`: `z1`'s array or fresh) and apart from `m1`, `m2`, `z2`, `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the run `mvJ` → `nat.subMod2N`'s entry -/
theorem runSm {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop) (sp pz lz cz n : Nat)
    (M : Memory) (hal : sp % 16 = 0) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp + 128) 320 false = true)
    (h152 : M.readLE (sp + 152) 8 = lz) (h264 : M.readLE (sp + 264) 8 = pz) (h160 : M.readLE (sp + 160) 8 = cz)
    (h184 : M.readLE (sp + 184) 8 = n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 mvJ) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 1805584 → S'.sp = S.sp → S'.mem = M →
      S'.regs 0 = BitVec.ofNat 64 pz → S'.regs 1 = BitVec.ofNat 64 lz → S'.regs 2 = BitVec.ofNat 64 cz →
      S'.regs 3 = BitVec.ofNat 64 pz → S'.regs 4 = BitVec.ofNat 64 lz → S'.regs 5 = BitVec.ofNat 64 cz →
      S'.regs 6 = S.regs 0 → S'.regs 7 = S.regs 4 → S'.regs 8 = S.regs 2 → S'.regs 9 = BitVec.ofNat 64 n →
      S'.regs 30 = BitVec.ofNat 64 smR → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e0 : S.regs 0 = x0 at KN
  generalize e2 : S.regs 2 = x2 at KN
  generalize e4 : S.regs 4 = x4 at KN
  generalize e18 : S.regs 18 = x18 at KN
  generalize e28 : S.regs 28 = x28 at KN
  generalize e29 : S.regs 29 = x29 at KN
  generalize eS : S.sp = xsp at KN
  subst hmem
  janus_run [h152, h264, h160, h184, hacc, hal] until [1805584]
  refine KN _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> first | omega | rfl | skip)
  rw [← eS, hsp]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

/-- a callee result in the destination's array or fresh (`subMod2N`'s `PostG` form) is a live local nat -/
theorem LN.of_sm (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
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
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
/-- the frames of a non-stack callee writing its window `cw` and `[pd, pd + 8 cd)` in the `stepC0` form, for a
located destination (`0 < cd`) or an EMPTY one (then as the destination `(0, 0)`) -/
theorem frm_dst (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd ld cd vd : Nat}
    (hd : LN R L s.mem st M L1 pd ld cd vd) {M' : Memory} {L2 : List (Nat × Nat)} (hx : LiveExt R L1 L2)
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 128)
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(pd, pd + 8 * cd)]))
    (hLF : LiveFrame M M' L1 [(pd, pd + 8 * cd)]) :
    ∃ qd kd : Nat, (∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      (∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(qd, qd + 8 * kd)]) ∧
      Apart qd (8 * kd) (sp - K) (K + 448) ∧
      MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [(qd, qd + 8 * kd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(qd, qd + 8 * kd)] ++ stkWs M st) ∧ StackBackL R L1 L2 st M M' ∧
      (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∧
      (∀ q c, 0 < c → (0 < cd → Apart q (8 * c) pd (8 * cd)) → Apart q (8 * c) qd (8 * kd)) := by
  have hcw := hP.st_cw hstk habove
  rcases Nat.eq_zero_or_pos cd with c0 | c0
  · subst c0
    have hF0 := SubMod2N.memFrame_drop_empty (by omega) hF
    have hL0 : LiveFrame M M' L1 [] :=
      SubMod2N.liveFrame_drop_empty (ws := []) (p := pd) (e := pd + 8 * 0) (by omega)
        (by rw [List.nil_append]; exact hLF)
    have hF1 : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ [((0 : Nat), 0 + 8 * 0)]) :=
      hF0.mono fun a n ho => by rw [outside_append] at ho; exact ho.1
    have hL1 : LiveFrame M M' L1 [((0 : Nat), 0 + 8 * 0)] := Expmc.liveFrame_widen hL0 fun _ _ _ => by simp only [outside_nil]
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF1 hL1 hcw out_00
    exact ⟨0, 0, fun _ _ _ _ => out_00, fun _ _ _ _ => out_00, by unfold Apart; omega, f1, f2, f3, f4,
      fun _ _ _ _ => by unfold Apart; omega⟩
  · have hloc := (hd.1.2.2 c0).1
    obtain ⟨w1, w2, -, -⟩ := Loc.ap hP hloc
    obtain ⟨f1, f2, f3, f4⟩ := nonStk h.sok hx hF hLF hcw (out1_of_apart w2)
    exact ⟨pd, cd, Loc.sub hloc, Loc.subL hloc, w1, f1, f2, f3, f4, fun _ _ hc h => h c0⟩

end

end FvModexp.Arm64.ExpEven
