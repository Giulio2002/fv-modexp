import FvModexp.Proofs.Arm64.Exp.LibOdd
import FvModexp.Proofs.Arm64.Exp.W4Fun
import FvModexp.Proofs.Arm64.Exp.W2Fun
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.expNNOdd` (arm64): statement layer and the windows' entry facts

`z.expNNOdd(stk, x, y, m)` (nat.go:1343-1358) is a 128-byte frame that calls `expNNOddMontgomeryWindowSize4` when
`len(y) > 1` (`threshold_for_4_bit_window / _W = 64 / 64 = 1`) and `expNNOddMontgomeryWindowSize2` otherwise, with the
same arguments. At its entry state `s` the frame of window-4 will be `sp = SP - 1056` (`SP - 128 - 928`), that of
window-2 `sp + 288` (`SP - 128 - 640`); both windows' windows lie in `[sp - K, sp + 1040)` (window-2 with `K + 288`),
inside `expNNOdd`'s own window `[sp - K, sp + 1168) = [SP - (K + 1056), SP + 112)` (the four argument spills go to
`SP + 8 .. SP + 96`).

* `OPre`: `W4En.EPre` with the larger window, plus `z` apart from the window (unconditionally: `z`'s range is in the
  windows' frames) and `stCap = 0 → stW = 0` (the stack's empty free part is then the point `0`, outside every slot).
* `epre4` / `epre2`: the windows' `EPre` at the callee entry state, after the prologue's stores.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpOdd

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOdd"

/-- the function's names (`LibOdd`: the windows' program and `nat.expNNOdd`) -/
abbrev names : List String := LibOdd.names

/-- entry (`0x1b70d0`) -/
abbrev fnO : Nat := 1798352
/-- return address of the window-4 call (`0x1b7104`) -/
abbrev r4 : Nat := 1798404
/-- return address of the window-2 call (`0x1b7114`) -/
abbrev r2 : Nat := 1798420

/-- an operand at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 1168) ∧ Apart a k st 24 ∧
    Apart a k (W4En.free M st).1 (W4En.free M st).2

/-- the call environment at the entry (`SP = sp + 1056`) -/
@[reducible] def OEnv (R : RtInv) (L : List (Nat × Nat)) (g sp K : Nat) (s : State) : Prop :=
  s.sp = BitVec.ofNat 64 (sp + 1056) ∧ s.regs 28 = BitVec.ofNat 64 g ∧
  g + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (g + 16) 8 false = true ∧ s.mem.readLE (g + 16) 8 + K < sp ∧
  Outside (g + 16) 8 ((sp - K, sp + 1168) :: R.rt) ∧ sp % 16 = 0 ∧ 4304 ≤ K ∧ K ≤ sp ∧ sp + 1168 ≤ 2 ^ 48 ∧
  s.mem.accessible (sp - K) (K + 1168) true = true ∧ LiveSep [(sp - K, sp + 1168)] R.rt ∧
  LiveSep L [(sp - K, sp + 1168)] ∧ Extracted.program.DataLoaded s.mem ∧ RunIface.Serves R

/-- the entry facts (as `W4En.EPre`, window `[sp - K, sp + 1168)`) -/
def OPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (g sp st zp zc xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  OEnv R L g sp K s ∧ K + 288 ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 1168)] ∧ RoOut R ∧
  Outside StackNat.wT 16 R.rt ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  OE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  OE R L sp K st s.mem yp (8 * ylen) ∧ s.mem.accessible yp (8 * ylen) false = true ∧ yp + 8 * ylen ≤ 2 ^ 48 ∧
    NatNorm s.mem yp ylen ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ 0 < xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ Apart zp (8 * zc) (sp - K) (K + 1168) ∧ (2 * n ≤ zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 1168) ∧ Apart st 24 (g + 16) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 1168) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8) ∧
  (stCap s.mem st = 0 → stW s.mem st = 0) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (W4En.free s.mem st).1 (W4En.free s.mem st).2 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  R.inv b L g (view R.rt L s.mem)

/-- the closed budget (the called window's) -/
def OBud (costF : Nat → Nat → Nat → Nat) (n xl ylen l : Nat) : Nat :=
  if 1 < ylen then ExpW4.W4Bud n xl (ExpW4.divCost costF n xl l) l else ExpW2.W2Bud n xl (ExpW2.divCost costF n xl l) l

/-- the cost the postcondition charges (the called window's) -/
def OCost (costF : Nat → Nat → Nat → Nat) (n xl ylen l : Nat) : Nat :=
  if 1 < ylen then ExpW4.W4Cost n xl (ExpW4.divCost costF n xl l) l else ExpW2.W2Cost n xl (ExpW2.divCost costF n xl l) l

/-- the precondition (entry state `s`, `sp = SP - 1056`) -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) : Prop :=
  OPre R b L K (s.regs 28).toNat (s.sp.toNat - 1056) st zp zc xp xl xc yp ylen mp n mc s ∧ st ≠ 0 ∧
  natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧
  stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n +
    2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16 ∧
  OBud costF n xl ylen (stLen s.mem st) ≤ b

/-- the postcondition (results `X0..X2`): `x^y mod m`, normalised, in `z`'s array or a fresh one -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (zp zc st xp xl yp ylen mp n : Nat) (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - OCost costF n xl ylen (stLen s.mem st) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K + 1056) 112 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-! ### Frame transfer of the entry facts -/

theorem ap_out {a k lo n : Nat} (h : Apart a k lo n) : Outside a k [(lo, lo + n)] := by
  unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega

theorem ap_sub {a k lo n lo' n' : Nat} (h : Apart a k lo n) (h1 : lo ≤ lo') (h2 : lo' + n' ≤ lo + n) :
    Apart a k lo' n' := by
  unfold Apart at h ⊢; omega

theorem globals_fr {R : RtInv} {m m' : Memory} {w w' : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' w) (hw : ∀ a n, Outside a n w → Outside a n w') : RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (hgw.of_sub (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

theorem norm_fr {m m' : Memory} {w : List (Nat × Nat)} (hF : MemFrame m m' w) {p n : Nat}
    (ho : Outside p (8 * n) w) (hn : NatNorm m p n) : NatNorm m' p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · exact Or.inl h0
  rcases hn with hn | hn
  · exact Or.inl hn
  · exact Or.inr (by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn)

set_option maxRecDepth 20000 in
/-- the stack header and its derived ranges survive a frame of the window -/
theorem hdr_fr {m m' : Memory} {sp K st : Nat} (hF : MemFrame m m' [(sp - K, sp + 1168)])
    (h : Apart st 24 (sp - K) (K + 1168)) (hK : K ≤ sp) :
    stW m' st = stW m st ∧ stLen m' st = stLen m st ∧ stCap m' st = stCap m st := by
  unfold Apart at h
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_⟩ <;>
    (simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
theorem oe_fr {R : RtInv} {L : List (Nat × Nat)} {sp K st W : Nat} {m m' : Memory} {a k : Nat}
    (e0 : stW m' st = stW m st) (e1 : stLen m' st = stLen m st) (e2 : stCap m' st = stCap m st)
    (h : OE R L sp K st m a k) (hW : W ≤ 1168) :
    (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + W) ∧ Apart a k st 24 ∧
      Apart a k (W4En.free m' st).1 (W4En.free m' st).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, ap_sub h2 (Nat.le_refl _) (by omega), h3, ?_⟩
  show Apart a k (stW m' st + 8 * stLen m' st) (8 * (stCap m' st - stLen m' st))
  rw [e0, e1, e2]; exact h4

set_option maxRecDepth 20000 in
theorem oe_fr2 {R : RtInv} {L : List (Nat × Nat)} {sp K st : Nat} {m m' : Memory} {a k : Nat}
    (e0 : stW m' st = stW m st) (e1 : stLen m' st = stLen m st) (e2 : stCap m' st = stCap m st)
    (h : OE R L sp K st m a k) :
    (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp + 288 - (K + 288)) (K + 288 + 752) ∧ Apart a k st 24 ∧
      Apart a k (W4En.free m' st).1 (W4En.free m' st).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := oe_fr (W := 1040) e0 e1 e2 h (by omega)
  exact ⟨h1, by rw [show sp + 288 - (K + 288) = sp - K by omega, show K + 288 + 752 = K + 1040 by omega]; exact h2, h3, h4⟩

set_option maxRecDepth 20000 in
/-- window-4's entry facts at the callee entry `S` (frame `sp`), from `OPre` at `s` and a frame of the window -/
theorem epre4 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp ylen mp n mc : Nat}
    {s S : State} (h : OPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s)
    (hF : MemFrame s.mem S.mem [(sp - K, sp + 1168)]) (hsp : S.sp = BitVec.ofNat 64 (sp + 928))
    (h28 : S.regs 28 = s.regs 28) (hrg : S.mem.regions = s.mem.regions) :
    W4En.EPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc S := by
  obtain ⟨⟨-, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩, hK20, hgl, hro, hty, hn, hn128,
    hmc0, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxl', hxp, hxc, hzp,
    hzc, hzW, hz, hgO, hsok, hstw, hstg, harr, hc0, hwbf, hwbA, hstf, hl16, hinv⟩ := h
  obtain ⟨e0, e1, e2⟩ := hdr_fr hF hstw hK'
  have hacc' := hF.accessible
  have hout : Outside (sp - K) (K + 1168) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1168 - (sp - K) = K + 1168 by omega] at this
  have ho : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1168) → Outside a k [(sp - K, sp + 1168)] := fun {a k} h' => by
    unfold Apart at h'; simp only [outside_cons, outside_nil, and_true]; omega
  refine ⟨⟨hsp, h28.trans hs28, hg1, by rw [hacc']; exact hg2, ?_, ?_, hal, hK, hK', by omega,
    by rw [hacc']; exact Memory.accessible_mono _ hacc (by omega) (by omega),
    LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega), LiveSep.sub_win hLs (by omega) (by omega),
    dataLoaded_frame (rt := []) (ws := [(sp - K, sp + 1168)]) hd hrg
      (fun d _ => trivial) (by rw [List.nil_append]; exact hF) (fun r hr _ => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        rw [show sp + 1168 - (sp - K) = K + 1168 by omega]; exact hacc), hsv⟩,
    by omega, globals_fr hgl hF (fun a k h' => by simp only [outside_cons, outside_nil, and_true] at h' ⊢; omega),
    hro, hty, hn, hn128, hmc0, hmc', oe_fr e0 e1 e2 hmO (by omega), by rw [hacc']; exact hma, hm48,
    norm_fr hF (ho hmO.2.1) hmN, oe_fr e0 e1 e2 hyO (by omega), by rw [hacc']; exact hya, hy48,
    norm_fr hF (ho hyO.2.1) hyN, hyl, hyl', oe_fr e0 e1 e2 hxO (by omega), by rw [hacc']; exact hxa, hx48,
    norm_fr hF (ho hxO.2.1) hxN, hxl, hxl', hxp, hxc, hzp, hzc, fun hz2 => ?_, oe_fr e0 e1 e2 hgO (by omega), ?_,
    ap_sub hstw (Nat.le_refl _) (by omega), hstg, ?_, by rw [hacc']; exact hwbf, hwbA, ?_, by rw [e1]; exact hl16,
    RtInv.inv_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 1168 - (sp - K) = K + 1168 by omega]; exact hout) hinv⟩
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hgo ⊢; omega)]; exact hg3
  · simp only [outside_cons] at hgo ⊢; exact ⟨by omega, hgo.2⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hz hz2
    exact ⟨oe_fr e0 e1 e2 a1 (by omega), by rw [hacc']; exact a2, a3, a4, a5, a6, a7⟩
  · exact (stkOK_frame hsok hF (ho hstw) (LiveExt.refl R L)).1
  · rw [e0, e2]; intro hc
    obtain ⟨a1, a2⟩ := harr hc
    exact ⟨ap_sub a1 (Nat.le_refl _) (by omega), a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [e0, e1, e2]; exact hstf

set_option maxRecDepth 20000 in
/-- window-2's entry facts at the callee entry `S` (frame `sp + 288`, `K + 288`), from `OPre` at `s` and a frame of the window -/
theorem epre2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp ylen mp n mc : Nat}
    {s S : State} (h : OPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s)
    (hF : MemFrame s.mem S.mem [(sp - K, sp + 1168)]) (hsp : S.sp = BitVec.ofNat 64 (sp + 288 + 640))
    (h28 : S.regs 28 = s.regs 28) (hrg : S.mem.regions = s.mem.regions) :
    W2En.EPre R b L (K + 288) g (sp + 288) st zp zc xp xl xc yp ylen mp n mc S := by
  obtain ⟨⟨-, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩, hK20, hgl, hro, hty, hn, hn128,
    hmc0, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxl', hxp, hxc, hzp,
    hzc, hzW, hz, hgO, hsok, hstw, hstg, harr, hc0, hwbf, hwbA, hstf, hl16, hinv⟩ := h
  obtain ⟨e0, e1, e2⟩ := hdr_fr hF hstw hK'
  have hacc' := hF.accessible
  have hout : Outside (sp - K) (K + 1168) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1168 - (sp - K) = K + 1168 by omega] at this
  have ho : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1168) → Outside a k [(sp - K, sp + 1168)] := fun {a k} h' => by
    unfold Apart at h'; simp only [outside_cons, outside_nil, and_true]; omega
  refine ⟨⟨hsp, h28.trans hs28, hg1, by rw [hacc']; exact hg2, ?_, ?_, by omega, by omega, by omega, by omega,
    by rw [hacc']; exact Memory.accessible_mono _ hacc (by omega) (by omega),
    LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega), LiveSep.sub_win hLs (by omega) (by omega),
    dataLoaded_frame (rt := []) (ws := [(sp - K, sp + 1168)]) hd hrg
      (fun d _ => trivial) (by rw [List.nil_append]; exact hF) (fun r hr _ => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        rw [show sp + 1168 - (sp - K) = K + 1168 by omega]; exact hacc), hsv⟩,
    by omega, globals_fr hgl hF (fun a k h' => by simp only [outside_cons, outside_nil, and_true] at h' ⊢; omega),
    hro, hty, hn, hn128, hmc0, hmc', oe_fr2 e0 e1 e2 hmO, by rw [hacc']; exact hma, hm48,
    norm_fr hF (ho hmO.2.1) hmN, oe_fr2 e0 e1 e2 hyO, by rw [hacc']; exact hya, hy48,
    norm_fr hF (ho hyO.2.1) hyN, hyl, hyl', oe_fr2 e0 e1 e2 hxO, by rw [hacc']; exact hxa, hx48,
    norm_fr hF (ho hxO.2.1) hxN, hxl, hxl', hxp, hxc, hzp, hzc, fun hz2 => ?_, oe_fr2 e0 e1 e2 hgO, ?_,
    ap_sub hstw (by omega) (by omega), hstg, ?_, by rw [hacc']; exact hwbf, hwbA, ?_, by rw [e1]; omega,
    RtInv.inv_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 1168 - (sp - K) = K + 1168 by omega]; exact hout) hinv⟩
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at hgo ⊢; omega)]; omega
  · simp only [outside_cons] at hgo ⊢; exact ⟨by omega, hgo.2⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hz hz2
    exact ⟨oe_fr2 e0 e1 e2 a1, by rw [hacc']; exact a2, a3, a4, a5, a6, a7⟩
  · exact (stkOK_frame hsok hF (ho hstw) (LiveExt.refl R L)).1
  · rw [e0, e2]; intro hc
    obtain ⟨a1, a2⟩ := harr hc
    exact ⟨ap_sub a1 (by omega) (by omega), a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [e0, e1, e2]; exact hstf

end FvModexp.Arm64.ExpOdd
