import FvModexp.Proofs.Amd64.Int.QRAt
import FvModexp.Proofs.Common.DivmcMem

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64): `QRPost`'s `IntPost` from `AtD` and the final stores (`post_of`) (pure)

The final stores (`finW`): `q.ptr` and `q.neg` (`q = t + 96`, `Mod`'s frame, in the window: `128 ≤ above`),
`z.len, z.cap, z.ptr = l, c, p` and `z.neg = 0`. Twin of the arm64 `IMod.post_of` (Arm64/Int/ModPost.lean; adapted from
expmc's `IExp.post_of`). Also: `y` is unchanged.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntOK IntPre IntPost IntV arrW)

theorem finW_read (Mw : Janus.Arm64.Memory) {qA zA q p l c qn a n : Nat}
    (h1 : a + n ≤ zA ∨ zA + 32 ≤ a) (h2 : a + n ≤ qA ∨ qA + 16 ≤ a) :
    (finW Mw qA zA q p l c qn).readLE a n = Mw.readLE a n := by
  simp only [finW]
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

theorem finW_hdr (Mw : Janus.Arm64.Memory) {qA zA q p l c qn : Nat} (hz : zA + 32 ≤ qA ∨ qA + 16 ≤ zA)
    (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64) :
    (finW Mw qA zA q p l c qn).readLE zA 1 = 0 ∧ (finW Mw qA zA q p l c qn).readLE (zA + 8) 8 = p ∧
      (finW Mw qA zA q p l c qn).readLE (zA + 16) 8 = l ∧ (finW Mw qA zA q p l c qn).readLE (zA + 24) 8 = c := by
  simp only [finW]
  refine ⟨Janus.Arm64.Memory.readLE_writeLE_self .., ?_, ?_, ?_⟩
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hp
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hl
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hc

theorem finW_frame (Mw : Janus.Arm64.Memory) (qA zA q p l c qn : Nat) :
    MemFrame Mw (finW Mw qA zA q p l c qn) [(zA, zA + 32), (qA, qA + 16)] := by
  simp only [finW]; janus_frame

theorem finW_acc (Mw : Janus.Arm64.Memory) (qA zA q p l c qn : Nat) (a n : Nat) (w : Bool) :
    (finW Mw qA zA q p l c qn).accessible a n w = Mw.accessible a n w := by
  simp only [finW, Janus.Arm64.Memory.accessible_writeLE]

theorem y_keep {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above zA yA t : Nat} {Mw M' : Janus.Arm64.Memory}
    (hkeep : ∀ a k, Held R L a k → Outside a k (win s stk above) → Outside a k (ZArr s.mem zA) →
      Mw.readLE a k = s.mem.readLE a k)
    (rdF : ∀ a n, (a + n ≤ zA ∨ zA + 32 ≤ a) → (a + n ≤ t ∨ t + 16 ≤ a) → M'.readLE a n = Mw.readLE a n)
    (hwT : ∀ a k, Outside a k (win s stk above) → a + k ≤ t ∨ t + 16 ≤ a)
    (hyH : Held R L yA 32) (hyW : Outside yA 32 (win s stk above)) (hzyH : zA + 32 ≤ yA ∨ yA + 32 ≤ zA)
    (hyzA : 0 < s.mem.readLE (zA + 24) 8 →
      Apart yA 32 (s.mem.readLE (zA + 8) 8) (8 * s.mem.readLE (zA + 24) 8))
    (hyL : NatLive s.mem R L (s.mem.readLE (yA + 8) 8) (s.mem.readLE (yA + 24) 8))
    (hylc : s.mem.readLE (yA + 16) 8 ≤ s.mem.readLE (yA + 24) 8)
    (hyO : 0 < s.mem.readLE (yA + 24) 8 →
      Outside (s.mem.readLE (yA + 8) 8) (8 * s.mem.readLE (yA + 24) 8) (win s stk above))
    (hzyA : 0 < s.mem.readLE (yA + 24) 8 →
      Apart zA 32 (s.mem.readLE (yA + 8) 8) (8 * s.mem.readLE (yA + 24) 8))
    (hzyArr : 0 < s.mem.readLE (zA + 24) 8 → 0 < s.mem.readLE (yA + 24) 8 →
      Apart (s.mem.readLE (zA + 8) 8) (8 * s.mem.readLE (zA + 24) 8) (s.mem.readLE (yA + 8) 8)
        (8 * s.mem.readLE (yA + 24) 8)) :
    IntV M' yA = IntV s.mem yA := by
  have hK : ∀ a k, Held R L a k → Outside a k (win s stk above) → Outside a k (ZArr s.mem zA) →
      (a + k ≤ zA ∨ zA + 32 ≤ a) → M'.readLE a k = s.mem.readLE a k := fun a k hH hW hZ hz =>
    (rdF a k hz (hwT a k hW)).trans (hkeep a k hH hW hZ)
  have hyZ : Outside yA 32 (ZArr s.mem zA) := outside_arrW hyzA
  have e8 := hK (yA + 8) 8 (hyH.sub (by omega) (by omega)) (hyW.of_sub (by omega) (by omega))
    (hyZ.of_sub (by omega) (by omega)) (by omega)
  have e16 := hK (yA + 16) 8 (hyH.sub (by omega) (by omega)) (hyW.of_sub (by omega) (by omega))
    (hyZ.of_sub (by omega) (by omega)) (by omega)
  simp only [RunIface.IntV]; rw [e8, e16]
  generalize s.mem.readLE (yA + 8) 8 = yp at hyL hyO hzyA hzyArr
  generalize s.mem.readLE (yA + 24) 8 = yc at hyL hyO hzyA hzyArr hylc
  generalize s.mem.readLE (yA + 16) 8 = yl at hylc ⊢
  rcases Nat.eq_zero_or_pos yl with h0 | h0
  · subst h0; rfl
  · have hyc : 0 < yc := by omega
    obtain ⟨-, hH, -, -⟩ := hyL hyc
    have hzA' := hzyA hyc; unfold Apart at hzA'
    exact hK _ _ (hH.sub (Nat.le_refl _) (by omega)) ((hyO hyc).of_sub (Nat.le_refl _) (by omega))
      ((outside_arrW (fun h => (hzyArr h hyc).symm)).of_sub (Nat.le_refl _) (by omega)) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`QuoRem`'s `IntPost`** for `z` and `y` kept, from `AtD` and the final stores -/
theorem post_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA] s) (hab : 128 ≤ above)
    {V p l c b' : Nat} {L' : List (Nat × Nat)} {Mw : Janus.Arm64.Memory}
    (hA : AtD R b B L stk above s zA V p l c b' L' Mw) (s' : State) {q qn : Nat}
    (hm : s'.mem = finW Mw ((s.regs 4).toNat + 96) zA q p l c qn) :
    IntPost R b B L stk above zA V s s' ∧ IntV s'.mem yA = IntV s.mem yA := by
  obtain ⟨⟨-, ⟨hst, -, -⟩, -, -, hrt, -, -, hLs, -⟩, -, -, -, -, hops, hpw⟩ := hpre
  simp only [regSP] at hst
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hpw
  obtain ⟨⟨hzyH, hzyA, hyzA, hzyArr⟩, -⟩ := hpw
  obtain ⟨⟨-, hz8, hz48, hzacc, hzH, -, -, -, hzap, -⟩, hzW, hzO, -, -, -, -⟩ := hoz
  obtain ⟨⟨-, -, hy48, -, hyH, hyL, hylc, -, -, -⟩, hyW, hyO, -, -, -, -⟩ := hoy
  generalize ht : (s.regs 4).toNat = t at *
  have hzH1 : Held R L' zA 32 := hA.ext.held hzH
  have hc40 := hA.c40; have hlc := hA.lc; have hp64 := hA.p64
  have hzW' := hzW; simp only [win, ht, outside_cons, outside_nil, and_true] at hzW'
  have hyW' := hyW; simp only [win, ht, outside_cons, outside_nil, and_true] at hyW'
  unfold Apart at hzyH
  -- the result array: apart from `z`'s header, held, outside the stack window
  have harr : 0 < c → Apart p (8 * c) zA 32 ∧ (p + 8 * c ≤ t - stk ∨ t + above ≤ p) := by
    intro hc
    rcases hA.orf with h0 | ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · omega
    · refine ⟨(hzap hc).symm, ?_⟩
      have := hzO hc; simp only [win, ht, outside_cons, outside_nil, and_true] at this; exact this
    · refine ⟨?_, ?_⟩
      · rcases hzH with h1 | h1
        · have := hap.apart_of_inRanges h1; unfold Apart; omega
        · exact (hin.apart h1).symm
      · have := hin.apart hrt; unfold Apart at this; omega
  have hzT : zA + 32 ≤ t + 96 ∨ t + 96 + 16 ≤ zA := by omega
  unfold IntPost
  rw [hm]
  have rdF : ∀ a n, (a + n ≤ zA ∨ zA + 32 ≤ a) → (a + n ≤ t + 96 ∨ t + 96 + 16 ≤ a) →
      (finW Mw (t + 96) zA q p l c qn).readLE a n = Mw.readLE a n := fun a n h1 h2 => finW_read Mw h1 h2
  have rdA : 0 < c → ∀ a n, p ≤ a → a + n ≤ p + 8 * c →
      (finW Mw (t + 96) zA q p l c qn).readLE a n = Mw.readLE a n := by
    intro hc a n h1 h2
    obtain ⟨hap, hor⟩ := harr hc
    unfold Apart at hap
    exact rdF a n (by omega) (by omega)
  obtain ⟨eN, eP, eL, eC⟩ := finW_hdr Mw (q := q) (qn := qn) (p := p) (l := l) (c := c) hzT hp64 (by omega) (by omega)
  have eV : natVal (finW Mw (t + 96) zA q p l c qn) p l = V := by
    rw [← hA.val]
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0; rfl
    · exact rdA (by omega) _ _ (Nat.le_refl _) (by omega)
  have eNorm : NatNorm (finW Mw (t + 96) zA q p l c qn) p l := by
    rcases hA.norm with h1 | h1
    · exact Or.inl h1
    · rcases Nat.eq_zero_or_pos l with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rw [rdA (by omega) _ _ (by omega) (by omega)]; exact h1)
  have hacc : ∀ a n w, (finW Mw (t + 96) zA q p l c qn).accessible a n w = Mw.accessible a n w :=
    finW_acc Mw (t + 96) zA q p l c qn
  -- the final stores as a frame
  have hFW := finW_frame Mw (t + 96) zA q p l c qn
  have hwR : Outside (t + 96) 16 R.rt := hrt.of_sub (by omega) (by omega)
  -- `y` unchanged
  have hyv : IntV (finW Mw (t + 96) zA q p l c qn) yA = IntV s.mem yA :=
    y_keep (fun a k hH hW hZ => hA.keep hH hW hZ) rdF (fun a k h => by
      simp only [win, ht, outside_cons, outside_nil, and_true] at h; omega) hyH hyW hzyH hyzA hyL hylc hyO hzyA hzyArr
  refine ⟨⟨?_, L', b', hA.ext, hA.bud, ?_, ⟨eN, hz8, hz48, ?_, hzH1, ?_, ?_, ?_, ?_, by rw [eC]; exact hc40⟩,
    ?_, ?_, ?_⟩, hyv⟩
  · simp only [RunIface.IntV]; rw [eP, eL, eV]
  · simp only [finW]
    rw [view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (Or.inr (hwR.of_sub (by omega) (by omega))),
      view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega)),
      view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (Or.inr (hwR.of_sub (by omega) (by omega)))]
    exact hA.inv
  · rw [hacc, hA.mf.accessible]; exact hzacc
  · rw [eP, eC]
    intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hA.live hc
    exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · rw [eL, eC]; exact hlc
  · rw [eP, eL]; exact eNorm
  · rw [eP, eC]; intro hc; exact ((harr hc).1).symm
  · rw [eP, eC]
    intro hc
    rcases hA.orf with h0 | h | h
    · omega
    · exact Or.inl h
    · exact Or.inr h
  · -- memory frame, byte by byte
    rw [← zarr_eq]
    refine MemFrame.of_bytes (fun a ho => ?_) (fun a k w => by rw [hacc, hA.mf.accessible])
    rw [outside_append, outside_append, outside_cons] at ho
    obtain ⟨⟨hoR, hoW⟩, hoZ, hoA⟩ := ho
    have hoW' := hoW; simp only [win, ht, outside_cons, outside_nil, and_true] at hoW'
    rw [MemFrame.byte hFW (by simp only [outside_cons, outside_nil, and_true] at hoZ ⊢; omega)]
    refine MemFrame.byte hA.mf ?_
    rw [outside_append, outside_append]; exact ⟨⟨hoR, hoW⟩, hoA⟩
  · rw [← zarr_eq]
    refine LiveFrame.of_bytes fun a hin ho => ?_
    rw [outside_cons] at ho
    obtain ⟨hoZ, hoA⟩ := ho
    obtain ⟨r, hr, e1, e2⟩ := hin
    have hLr := hLs r hr; simp only [win, ht, outside_cons, outside_nil, and_true] at hLr
    rw [MemFrame.byte hFW (by simp only [outside_cons, outside_nil, and_true] at hoZ ⊢; omega)]
    exact LiveFrame.byte hA.lf ⟨r, hr, e1, e2⟩ hoA

end FvModexp.Amd64.IMod
