import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Common.ExpOdd

/-!
# `expNNOddMontgomeryWindowSize2` (arm64), main loop nat.go:1580-1606: shared definitions

The loop is proved in three modules: `W2Body1` (loop test → after the 2nd squaring), `W2Body2` (the multiplication by `powers[yi >> 62]` → back at
the test, the `z, zz = zz, z` swap done), `W2Loop` (induction on `33·i + c`, outer step `i--; yi = y[i]; k = 31`, exit). All in
continuation-passing form over an anchor memory `M0` (the memory at the first arrival at the test).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Loop

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2"
/-- the loop test `TBZ $63, R21` -/
abbrev test : Nat := segAddr LibExp.program fn + 0xa10
/-- the loop exit (after `if i == 0 { break }`): the final `zz.montgomery(z, one, …)` -/
abbrev exit : Nat := segAddr LibExp.program fn + 0xa28

/-- the window step of `expNNOddMont 2` (ExpOdd.lean) -/
abbrev step (n Mv k : Nat) (tbl : Nat → Nat) (z d : Nat) : Nat :=
  Exp.montgomery n (Exp.iter (fun z => Exp.montgomery n z z Mv k) 2 z) (tbl d) Mv k

/-- per-array facts of the two Montgomery buffers `z`, `zz` (writable, roomy, held, apart from the call windows) -/
@[reducible] def Buf (R : RtInv) (L : List (Nat × Nat)) (g sp n : Nat) (M0 : Memory) (p c : Nat) : Prop :=
  2 * n ≤ c ∧ c < 2 ^ 40 ∧ M0.accessible p (8 * c) true = true ∧ p + 8 * c ≤ 2 ^ 48 ∧
  (InRanges p (8 * c) L ∨ Outside p (8 * c) R.rt) ∧ Apart p (8 * c) (sp - 4288) (4288 + 752) ∧
  Apart (g + 16) 8 p (8 * c)

/-- the frame ranges the loop writes (callee windows + spills), without the two buffers -/
@[reducible] def fw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4288, sp - 8), (sp + 8, sp + 224), (sp + 232, sp + 336), (sp + 368, sp + 432), (sp + 576, sp + 584),
    (sp + 616, sp + 624)]

/-- everything the loop may change since the anchor `M0` -/
@[reducible] def lw (R : RtInv) (sp zp zc zzp zzc : Nat) : List (Nat × Nat) :=
  R.rt ++ fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]

/-- a read-only input `p[0:n]` (readable, held, apart from the whole window `[sp-4288, sp+752)`) -/
@[reducible] def Inp (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧
  Apart p (8 * n) (sp - 4288) (4288 + 752)

/-- the stack/guard environment of the loop at the anchor `M0` -/
@[reducible] def Env (R : RtInv) (L : List (Nat × Nat)) (g sp : Nat) (M0 : Memory) : Prop :=
  sp % 16 = 0 ∧ 4288 ≤ sp ∧ sp + 752 ≤ 2 ^ 48 ∧ M0.accessible (sp - 4288) (4288 + 752) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M0.accessible (g + 16) 8 false = true ∧ M0.readLE (g + 16) 8 + 4288 < sp ∧
  Outside (sp - 4288) (4288 + 752) R.rt ∧ Apart (g + 16) 8 (sp - 4288) (4288 + 752) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - 4288, sp + 752)]

theorem mcall_of {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc rp rc xp yp : Nat} {M0 : Memory}
    (he : Env R L g sp M0) (hn : 0 < n) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hr : Buf R L g sp n M0 rp rc)
    (hx : Inp R L sp n M0 xp) (hy : Inp R L sp n M0 yp) (hm : Inp R L sp n M0 mp)
    (hrx : Apart rp (8 * rc) xp (8 * n)) (hry : Apart rp (8 * rc) yp (8 * n)) (hrm : Apart rp (8 * rc) mp (8 * n))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n]) :
    MontW.MCall R L g (M0.readLE (g + 16) 8) sp n mp mc rp rc xp yp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hr
  have sub : ∀ p k, Apart p k (sp - 4288) (4288 + 752) → Apart p k (sp - 4288) (4288 + 120) := by
    intro p k h; unfold Apart at h ⊢; omega
  refine ⟨h1, h2, by omega, h5, h7,
    h8.of_sub (Nat.le_refl _) (by omega), sub _ _ h9, h10, ?_, hn, r1, r2, hmc, hmc', r4, r5, sub _ _ r6, r7,
    ⟨hx.2.1, hx.2.2.1, sub _ _ hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, sub _ _ hy.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, hok.1, hok.2⟩
  intro r hr
  have := h11 r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- `LSR $62` as the executor states it (rotate + mask) -/
theorem rot62 (yi : Nat) (h : yi < 2 ^ 64) :
    ((BitVec.ofNat 64 yi).rotateRight 62).toNat % 4 = yi / 4611686018427387904 := by
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.or_mod_two_pow, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 : yi * 2 ^ (64 - 62 % 64) % 2 ^ 64 % 2 ^ 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide)]; simp [Nat.mul_mod_left]
  rw [h1, Nat.or_zero]
  have : yi / 2 ^ (62 % 64) < 2 ^ 2 := by simp; omega
  rw [Nat.mod_eq_of_lt this]

/-- `LSL $2` as the executor states it (rotate + masks) -/
theorem lsl2 (x : BitVec 64) :
    x.rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64 = x <<< 2 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551612#64)[i] = decide (2 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 2
  · simp [h]
  · simp [h]; omega

theorem lsl2' (yi : Nat) :
    (BitVec.ofNat 64 yi).rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64 =
      BitVec.ofNat 64 ((yi * 2 ^ 2) % 2 ^ 64) := by
  rw [lsl2]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- a read of an object apart from the loop window is not affected by a spill-slot store (cheap `simp` discharger) -/
theorem rd_slot {sp X l K : Nat} (h : Apart X l (sp - 4288) (4288 + 752)) (hs : 4288 ≤ sp) (hK : K + 8 ≤ 752) :
    X + l ≤ sp + K ∨ sp + K + 8 ≤ X := by
  unfold Apart at h; omega

/-- the static facts of the loop (anchor memory `M0` = the memory at the first arrival at the test) -/
def Static (R : RtInv) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat)
    (M0 : Memory) : Prop :=
  Env R L g sp M0 ∧ 0 < n ∧ n ≤ 2 ^ 16 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧ k0 < 2 ^ 64 ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  Inp R L sp n M0 mp ∧ Inp R L sp ylen M0 yp ∧ M0.readLE yp (8 * ylen) = Y ∧
  (∀ d, d < 4 → Inp R L sp n M0 (pp d) ∧ M0.readLE (pp d) (8 * n) = tbl d ∧ pcap d < 2 ^ 64 ∧
    M0.readLE (sp + 432 + 24 * d) 8 = pp d ∧ M0.readLE (sp + 440 + 24 * d) 8 = n ∧
    M0.readLE (sp + 448 + 24 * d) 8 = pcap d) ∧
  M0.readLE (sp + 728) 8 = mp ∧ M0.readLE (sp + 736) 8 = n ∧ M0.readLE (sp + 744) 8 = mc ∧
  M0.readLE (sp + 224) 8 = k0 ∧ M0.readLE (sp + 712) 8 = ylen ∧ M0.readLE (sp + 704) 8 = yp ∧
  (∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])

/-- the two buffers at a loop state -/
@[reducible] def Bufs (R : RtInv) (L : List (Nat × Nat)) (g sp n mp yp ylen : Nat) (pp : Nat → Nat)
    (ext : List (Nat × Nat)) (M0 : Memory)
    (zp zc zzp zzc : Nat) : Prop :=
  Buf R L g sp n M0 zp zc ∧ Buf R L g sp n M0 zzp zzc ∧ Apart zp (8 * zc) zzp (8 * zzc) ∧
  Apart zp (8 * zc) mp (8 * n) ∧ Apart zzp (8 * zzc) mp (8 * n) ∧
  Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
  (∀ d, d < 4 → Apart zp (8 * zc) (pp d) (8 * n) ∧ Apart zzp (8 * zzc) (pp d) (8 * n)) ∧
  zp % 8 = 0 ∧ zzp % 8 = 0 ∧ Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zzp (8 * zzc) (sp - 4304) 16 ∧
  (∀ q ∈ ext, Apart zp (8 * zc) q.1 q.2 ∧ Apart zzp (8 * zzc) q.1 q.2)

theorem Bufs.swap {R : RtInv} {L : List (Nat × Nat)} {g sp n mp yp ylen : Nat} {pp : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    {zp zc zzp zzc : Nat} (h : Bufs R L g sp n mp yp ylen pp ext M0 zp zc zzp zzc) :
    Bufs R L g sp n mp yp ylen pp ext M0 zzp zzc zp zc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  exact ⟨a2, a1, a3.symm, a5, a4, a7, a6, fun d hd => ⟨(a8 d hd).2, (a8 d hd).1⟩, a10, a9, a12, a11,
    fun q hq => ⟨(a13 q hq).2, (a13 q hq).1⟩⟩

/-- the memory facts at a loop state `M` -/
@[reducible] def Mem (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M0 M : Memory) (zp zc zzp zzc : Nat) :
    Prop :=
  MemFrame M0 M (lw R sp zp zc zzp zzc) ∧ LiveFrame M0 M L [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)] ∧
  R.inv b L g (view R.rt L M) ∧ M.regions = M0.regions
/-- the frame facts of a loop state since the anchor `M0` -/
@[reducible] def FL (R : RtInv) (L : List (Nat × Nat)) (sp zp zc zzp zzc : Nat) (M0 M : Memory) : Prop :=
  MemFrame M0 M (lw R sp zp zc zzp zzc) ∧ LiveFrame M0 M L [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]

theorem FL.write {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M : Memory}
    (h : FL R L sp zp zc zzp zzc M0 M) (hLs : LiveSep L [(sp - 4288, sp + 752)]) {a k : Nat} (v : Nat)
    (hw : (sp - 4288 ≤ a ∧ a + k ≤ sp - 8) ∨ (sp + 8 ≤ a ∧ a + k ≤ sp + 224) ∨ (sp + 232 ≤ a ∧ a + k ≤ sp + 336) ∨
      (sp + 368 ≤ a ∧ a + k ≤ sp + 432) ∨ (sp + 576 ≤ a ∧ a + k ≤ sp + 584) ∨ (sp + 616 ≤ a ∧ a + k ≤ sp + 624)) :
    FL R L sp zp zc zzp zzc M0 (M.writeLE a k v) := by
  refine ⟨h.1.writeLE_inRanges v ?_, h.2.writeLE v (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))⟩
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4288, sp - 8), by simp [lw, fw], h1, h2⟩
  · exact ⟨(sp + 8, sp + 224), by simp [lw, fw], h1, h2⟩
  · exact ⟨(sp + 232, sp + 336), by simp [lw, fw], h1, h2⟩
  · exact ⟨(sp + 368, sp + 432), by simp [lw, fw], h1, h2⟩
  · exact ⟨(sp + 576, sp + 584), by simp [lw, fw], h1, h2⟩
  · exact ⟨(sp + 616, sp + 624), by simp [lw, fw], h1, h2⟩

theorem FL.call {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M M' : Memory} {rp rc : Nat}
    (h : FL R L sp zp zc zzp zzc M0 M) (hc : MemFrame M M' (R.rt ++ [(sp - 4288, sp - 8), (sp + 8, sp + 120)] ++ [(rp, rp + 8 * rc)]))
    (hl : LiveFrame M M' L [(rp, rp + 8 * rc)]) (hr : (rp = zp ∧ rc = zc) ∨ (rp = zzp ∧ rc = zzc)) :
    FL R L sp zp zc zzp zzc M0 M' := by
  refine ⟨h.1.trans hc (fun a n ho => ⟨ho, ?_⟩),
    h.2.trans (FvModexp.Expmc.liveFrame_widen hl (fun a n ho => ?_)) (fun _ _ h => h)⟩
  · simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 e2 <;> omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 e2 <;> omega

theorem FL.swap {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M : Memory}
    (h : FL R L sp zp zc zzp zzc M0 M) : FL R L sp zzp zzc zp zc M0 M := by
  refine ⟨(MemFrame.refl M0 []).trans h.1 (fun a n ho => ⟨trivial, ?_⟩),
    FvModexp.Expmc.liveFrame_widen h.2 (fun a n ho => ?_)⟩
  · simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega

/-- a held input outside the loop's window and buffers reads as at the anchor -/
theorem FL.read {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M : Memory} {a n : Nat}
    (h : FL R L sp zp zc zzp zzc M0 M) (hh : InRanges a n L ∨ Outside a n R.rt)
    (h1 : Apart a n (sp - 4288) (4288 + 752)) (hs : 4288 ≤ sp) (h2 : Apart zp (8 * zc) a n)
    (h3 : Apart zzp (8 * zzc) a n) : M.readLE a n = M0.readLE a n := by
  unfold Apart at h1 h2 h3
  exact FvModexp.Expmc.held_readLE hh h.1 h.2 (by simp only [fw, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)

/-- the return point of the 2nd squaring `z = z.montgomery(zz, zz, …)` (nat.go:1454) -/
abbrev mid : Nat := segAddr LibExp.program fn + 0x974

/-- one squaring of the window step -/
abbrev sq (n Mv k z : Nat) : Nat := Exp.montgomery n z z Mv k

theorem step_eq (n Mv k : Nat) (tbl : Nat → Nat) (z d : Nat) :
    step n Mv k tbl z d = Exp.montgomery n (sq n Mv k (sq n Mv k z)) (tbl d) Mv k := rfl

theorem outer_succ (st : Nat → Nat → Nat) (Y i yi c z : Nat) :
    Exp.outerLoop 2 st Y 32 i yi (c + 1) z =
      Exp.outerLoop 2 st Y 32 i ((yi * 2 ^ 2) % Exp.B) c (st z (yi / 2 ^ (64 - 2))) := by
  cases i <;> rfl

theorem outer_zero (st : Nat → Nat → Nat) (Y i yi z : Nat) :
    Exp.outerLoop 2 st Y 32 (i + 1) yi 0 z = Exp.outerLoop 2 st Y 32 i (Exp.wd Y i) 32 z := rfl

theorem outer_done (st : Nat → Nat → Nat) (Y yi z : Nat) : Exp.outerLoop 2 st Y 32 0 yi 0 z = z := rfl

end FvModexp.Arm64.W2Loop
