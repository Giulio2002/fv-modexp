import FvModexp.Proofs.Amd64.Int.QRB
import FvModexp.Proofs.Amd64.Int.QRLem
import FvModexp.Proofs.Common.ByteFrame

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64): the facts before the final header stores (`AtD`, `atD_of`) (pure)

`AtD … M`: the remainder `(p, l, c)` holds `V`, normalised, cap `< 2^40`, live in `L'`, `z`'s old array or a fresh one;
`M` (the memory after `nat.div`, `q`'s `len, cap` stores and the barrier) differs from `QuoRem`'s entry memory only in
`R.rt`, the window and `z`'s old array (byte-granular frames: an empty `z` has an arbitrarily placed array).
Twin of the arm64 `IMod.AtD`/`atD_of` (Arm64/Int/ModAt.lean; `ZArr`, `out_arrW`, `outside_arrW` adapted from expmc's
`IExp.AtN`). Here `t` = `QuoRem`'s entry `RSP`; segment A wrote `[t-120, t-64) ∪ [t-8, t) ∪ [t+8, t+40)`; `nat.div`
ran at `RSP = t - 120`; `q`'s header is at `t + 96` (in `Mod`'s frame, inside the window: `128 ≤ above`); the barrier's
frame is `[t-4216, t-112)` (`runQB`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntOK IntPre IntPost IntV arrW)
open FvModexp.Amd64.ExpHyp (NatOF)
open FvModexp.Amd64.EvenHyp (RtPost)

/-- `RunIface.arrW` behind an irreducible name (expmc s34 PERF LESSON: its `if` is evaluated by `whnf`) -/
@[irreducible] def ZArr (m : Janus.Arm64.Memory) (zA : Nat) : List (Nat × Nat) := arrW m zA

theorem zarr_eq (m : Janus.Arm64.Memory) (zA : Nat) : ZArr m zA = arrW m zA := by unfold ZArr; rfl

/-- a byte outside `z`'s old array as a written range is outside the range `(p, p + 8 c)` of its header fields -/
theorem out_arrW {m : Janus.Arm64.Memory} {zA a : Nat} (h : Outside a 1 (ZArr m zA)) :
    Outside a 1 [(m.readLE (zA + 8) 8, m.readLE (zA + 8) 8 + 8 * m.readLE (zA + 24) 8)] := by
  rw [zarr_eq] at h
  unfold arrW at h
  generalize m.readLE (zA + 8) 8 = p at h ⊢
  generalize m.readLE (zA + 24) 8 = c at h ⊢
  split at h
  · exact h
  · have : c = 0 := by omega
    subst this; exact outside1_empty a p

/-- a range apart from `z`'s old array (when it exists) is outside it as a written range -/
theorem outside_arrW {m : Janus.Arm64.Memory} {zA a k : Nat}
    (h : 0 < m.readLE (zA + 24) 8 → Apart a k (m.readLE (zA + 8) 8) (8 * m.readLE (zA + 24) 8)) :
    Outside a k (ZArr m zA) := by
  rw [zarr_eq]
  unfold arrW
  generalize m.readLE (zA + 8) 8 = p at h ⊢
  generalize m.readLE (zA + 24) 8 = c at h ⊢
  split
  · rename_i hc
    have := h hc; unfold Apart at this
    simp only [outside_cons, outside_nil, and_true]; omega
  · exact trivial

/-- the facts before the final stores (memory `M`; remainder `(p, l, c)` holding `V`, live set `L'`, budget `b'`) -/
structure AtD (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (stk above : Nat) (s : State) (zA V p l c b' : Nat)
    (L' : List (Nat × Nat)) (M : Janus.Arm64.Memory) : Prop where
  val : natVal M p l = V
  norm : NatNorm M p l
  lc : l ≤ c
  c40 : c < 2 ^ 40
  p64 : p < 2 ^ 64
  ext : LiveExt R L L'
  bud : b - B ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  live : NatLive M R L' p c
  orf : c = 0 ∨ (p = s.mem.readLE (zA + 8) 8 ∧ c = s.mem.readLE (zA + 24) 8) ∨
    (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s stk above ++ ZArr s.mem zA)
  lf : LiveFrame s.mem M L (ZArr s.mem zA)

/-- a held range outside the window and `z`'s old array is unchanged up to `M` -/
theorem AtD.keep {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA V p l c b' : Nat}
    {L' : List (Nat × Nat)} {M : Janus.Arm64.Memory} (hA : AtD R b B L stk above s zA V p l c b' L' M) {a k : Nat}
    (hH : Held R L a k) (hW : Outside a k (win s stk above)) (hZ : Outside a k (ZArr s.mem zA)) :
    M.readLE a k = s.mem.readLE a k := by
  rcases hH with hi | ho
  · exact hA.lf.readLE a k hi hZ
  · refine hA.mf.readLE a k ?_
    rw [outside_append, outside_append]
    exact ⟨⟨ho, hW⟩, hZ⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`AtD`** before the final stores, from `QRPre`'s `IntPre`, segment A's frame, `DivPostM`'s pieces and segment
B's barrier facts (`Mw`) -/
theorem atD_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA] s) (h4224 : 4224 ≤ stk) (hab : 128 ≤ above)
    {stkD aboveD : Nat} (hstkD : stkD + 120 ≤ stk) (habD : aboveD ≤ 112)
    {zp zl zc yp yl : Nat}
    (ez8 : s.mem.readLE (zA + 8) 8 = zp) (ez16 : s.mem.readLE (zA + 16) 8 = zl)
    (ez24 : s.mem.readLE (zA + 24) 8 = zc)
    (ey8 : s.mem.readLE (yA + 8) 8 = yp) (ey16 : s.mem.readLE (yA + 16) 8 = yl)
    {cost : Nat → Nat → Nat} (hcost : cost zl yl ≤ B)
    {S3 S4 : State} (hsp3 : (S3.regs 4).toNat = (s.regs 4).toNat - 120)
    (hF3 : MemFrame s.mem S3.mem [((s.regs 4).toNat - 120, (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 40)])
    {r rl rc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    (hr : NatOF R L L' S4.mem zp zc 1 r rl rc (natVal S3.mem zp zl % natVal S3.mem yp yl))
    (hrt' : RtPost R b (cost zl yl) L L' b' S3 S4)
    (hMF : MemFrame S3.mem S4.mem (R.rt ++ win S3 stkD aboveD ++ [(zp, zp + 8 * zc)]))
    (hLF : LiveFrame S3.mem S4.mem L [(zp, zp + 8 * zc)])
    (hr64 : r < 2 ^ 64) {qA ql qc : Nat} (hqA : qA = (s.regs 4).toNat + 96) {Mw : Janus.Arm64.Memory}
    (hMw : MemFrame (hdrQ S4.mem qA ql qc) Mw (R.rt ++ [((s.regs 4).toNat - 4216, (s.regs 4).toNat - 112)]))
    (hLw : LiveFrame (hdrQ S4.mem qA ql qc) Mw L' [])
    (hIw : R.inv b' L' (s.regs 14).toNat (view R.rt L' Mw)) :
    AtD R b B L stk above s zA (IntV s.mem zA % IntV s.mem yA) r rl rc b' L' Mw := by
  obtain ⟨⟨-, ⟨hst, -, -⟩, -, -, hrt, -, -, hLs, -⟩, -, -, -, -, hops, -⟩ := hpre
  simp only [regSP] at hst
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  clear hops
  obtain ⟨⟨-, -, -, -, -, -, hzlc, -, -, -⟩, -, hzO, -, -, -, -⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, -, hylc, -, -, -⟩, -, hyO, -, -, -, -⟩ := hoy
  obtain ⟨hv, hnm, hlc, hc40, hnl, hd⟩ := hr
  obtain ⟨hx, hb, -⟩ := hrt'
  subst hqA
  generalize ht : (s.regs 4).toNat = t at *
  have hF3w : MemFrame s.mem S3.mem [(t - stk, t + above)] :=
    hF3.mono fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hvw : ∀ {a q k : Nat}, s.mem.readLE (a + 8) 8 = q → s.mem.readLE (a + 16) 8 = k →
      k ≤ s.mem.readLE (a + 24) 8 →
      (0 < s.mem.readLE (a + 24) 8 → Outside (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8)
        (win s stk above)) → natVal S3.mem q k = natVal s.mem q k := by
    intro a q k e8 e16 hlc' hO
    subst e8
    refine natVal_frame' hF3w fun h => ?_
    have := hO (by omega); rw [win, ht] at this
    exact this.of_sub (Nat.le_refl _) (by omega)
  have evz := hvw ez8 ez16 (ez16 ▸ hzlc) hzO
  have evy := hvw ey8 ey16 (ey16 ▸ hylc) hyO
  rw [evz, evy] at hv
  have hz' : 0 < zc → zp + 8 * zc ≤ t - stk ∨ t + above ≤ zp := fun h => by
    have := hzO (ez24 ▸ h); rw [ez8, ez24, win, ht] at this
    simp only [outside_cons, outside_nil, and_true] at this; exact this
  rw [win, hsp3] at hMF
  -- the remainder's array is held in `L'` or outside `R.rt`, and outside the window
  have harr : 0 < rc → Held R L' r (8 * rc) ∧ (r + 8 * rc ≤ t - stk ∨ t + above ≤ r) := by
    intro hc
    refine ⟨(hnl hc).2.1, ?_⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · exact hz' hc
    · have := hin.apart hrt; unfold Apart at this; omega
  have hQ : MemFrame S4.mem (hdrQ S4.mem (t + 96) ql qc) [(t + 96 + 16, t + 96 + 32)] := by
    simp only [hdrQ]; janus_frame
  -- bytes of the remainder's array: `S4 → Mw` unchanged
  have hS4w : ∀ a, 0 < rc → r ≤ a → a + 1 ≤ r + 8 * rc → Mw.bytes a = S4.mem.bytes a := by
    intro a hc h1 h2
    obtain ⟨hH, hO⟩ := harr hc
    have e1 : (hdrQ S4.mem (t + 96) ql qc).bytes a = S4.mem.bytes a :=
      MemFrame.byte hQ (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [← e1]
    rcases hH with hi | ho
    · exact LiveFrame.byte hLw (hi.sub h1 h2) trivial
    · exact MemFrame.byte hMw (by
        rw [outside_append]
        exact ⟨ho.of_sub h1 h2, by simp only [outside_cons, outside_nil, and_true]; omega⟩)
  have hrdR : ∀ a k, 0 < rc → r ≤ a → a + k ≤ r + 8 * rc → Mw.readLE a k = S4.mem.readLE a k := fun a k hc h1 h2 =>
    Janus.Arm64.Memory.readLE_congr fun i hi => hS4w (a + i) hc (by omega) (by omega)
  have hacc : ∀ a k w, Mw.accessible a k w = S4.mem.accessible a k w := fun a k w => by
    rw [hMw.accessible]; simp only [hdrQ, Janus.Arm64.Memory.accessible_writeLE]
  refine ⟨?_, ?_, hlc, hc40, hr64, hx, by omega, hIw, ?_, ?_, ?_, ?_⟩
  · have eV : IntV s.mem zA % IntV s.mem yA = natVal s.mem zp zl % natVal s.mem yp yl := by
      simp only [RunIface.IntV]; rw [ez8, ez16, ey8, ey16]
    rw [eV, ← hv]
    rcases Nat.eq_zero_or_pos rl with hl | hl
    · subst hl; rfl
    · exact hrdR _ _ (by omega) (Nat.le_refl _) (by omega)
  · rcases hnm with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos rl with hl | hl
      · exact Or.inl hl
      · exact Or.inr (by rw [hrdR _ _ (by omega) (by omega) (by omega)]; exact h)
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hnl hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · rcases Nat.eq_zero_or_pos rc with hc | hc
    · exact Or.inl hc
    · rw [ez8, ez24]
      rcases hd with h | ⟨-, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · -- memory frame, byte by byte
    refine MemFrame.of_bytes (fun a ho => ?_) (fun a k w => by
      rw [hacc, hMF.accessible, hF3.accessible])
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hoR, hoW⟩, hoA⟩ := ho
    have h3 := out_arrW hoA; rw [ez8, ez24] at h3
    simp only [win, ht, outside_cons, outside_nil, and_true] at hoW
    rw [MemFrame.byte hMw (by
        rw [outside_append]; exact ⟨hoR, by simp only [outside_cons, outside_nil, and_true]; omega⟩),
      MemFrame.byte hQ (by simp only [outside_cons, outside_nil, and_true]; omega),
      MemFrame.byte hMF (by
        rw [outside_append, outside_append]
        exact ⟨⟨hoR, by simp only [outside_cons, outside_nil, and_true]; omega⟩, h3⟩)]
    exact MemFrame.byte hF3 (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine LiveFrame.of_bytes fun a hin ho => ?_
    have h3 := out_arrW ho; rw [ez8, ez24] at h3
    obtain ⟨q, hq, e1, e2⟩ := hin
    have hLq := hLs q hq; rw [win, ht] at hLq
    simp only [outside_cons, outside_nil, and_true] at hLq
    rw [LiveFrame.byte hLw (hx.inRanges_old ⟨q, hq, e1, e2⟩) trivial,
      MemFrame.byte hQ (by simp only [outside_cons, outside_nil, and_true]; omega),
      LiveFrame.byte hLF ⟨q, hq, e1, e2⟩ h3]
    exact MemFrame.byte hF3 (by simp only [outside_cons, outside_nil, and_true]; omega)

end FvModexp.Amd64.IMod
