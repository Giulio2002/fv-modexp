import FvModexp.Proofs.Amd64.Exp.IExpDefs
import FvModexp.Proofs.Amd64.Exp.IExpD

/-! # `(*Int).exp` (amd64; agent expmc s77, twin of the arm64 IExpPost): `IntPost` from `AtN` and segment D's
continuation facts (`post_of`) (pure) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IExp

open FvModexp.Amd64.RunIface (IntOK IntPre IntPost IntV arrW)

/-- the bytes segment D writes and `(*Int).exp`'s whole frame -/
theorem out_post {rt : List (Nat × Nat)} {t stk above zA a : Nat} {ws : List (Nat × Nat)} (h4416 : 0x1138 ≤ stk)
    (ho : Outside a 1 (rt ++ [(t - stk, t + above)] ++ (zA, zA + 32) :: ws)) :
    Outside a 1 [(zA, zA + 32)] ∧ Outside a 1 (rt ++ [(t - 0x1138, t - 0x130)]) ∧
      Outside a 1 (rt ++ [(t - stk, t + above)] ++ ws) := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
  obtain ⟨⟨hR, hW1⟩, hZ, hws⟩ := ho
  exact ⟨hZ, ⟨hR, by omega⟩, ⟨hR, hW1⟩, hws⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`IntPost`** (and the result's cap bound) from `AtN` and segment D's continuation facts: `Mw` the memory after
the header stores `len, cap` and (barrier on) the buffer stores, the final stores `z.abs.ptr = p`, `z.neg = 0` -/
theorem post_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (h0x1138 : 0x1138 ≤ stk) (hab : 48 ≤ above)
    {V p l c b' : Nat} {L' : List (Nat × Nat)} {M : Janus.Arm64.Memory}
    (hA : AtN R b B L stk above s zA V p l c b' L' M) {Mw : Janus.Arm64.Memory}
    (hMw : MemFrame (hdrW M zA l c) Mw (R.rt ++ [((s.regs 4).toNat - 0x1138, (s.regs 4).toNat - 0x130)]))
    (hLw : LiveFrame (hdrW M zA l c) Mw L' [])
    (hIw : R.inv b' L' (s.regs 14).toNat (view R.rt L' Mw))
    (s' : State) (hm : s'.mem = (Mw.writeLE (zA + 8) 8 p).writeLE zA 1 0) :
    IntPost R b B L stk above zA V s s' ∧ s'.mem.readLE (zA + 24) 8 < 2 ^ 40 := by
  obtain ⟨⟨-, ⟨hstk, -, -⟩, -, -, hrt, -, -, -, -, -⟩, -, -, -, -, hops, -⟩ := hpre
  obtain ⟨⟨-, hz8, hz48, hzacc, hzH, -, -, -, hzap, -⟩, hzW, hzO, -, -, -, -⟩ := hops zA (by simp)
  clear hops
  have hst : stk ≤ (s.regs 4).toNat := hstk
  have hzH1 : Held R L' zA 32 := hA.ext.held hzH
  have hc40 := hA.c40; have hlc := hA.lc; have hp64 := hA.p64
  simp only [win, outside_cons, outside_nil, and_true] at hzW
  -- the result array: apart from `z`'s header, held, outside the stack window
  have harr : 0 < c → Apart p (8 * c) zA 32 ∧ (InRanges p (8 * c) L' ∨
      (Outside p (8 * c) R.rt ∧ (p + 8 * c ≤ (s.regs 4).toNat - stk ∨ (s.regs 4).toNat + above ≤ p))) := by
    intro hc
    obtain ⟨-, hH, -, -⟩ := hA.live hc
    rcases hA.orf with h0 | ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · omega
    · refine ⟨(hzap hc).symm, ?_⟩
      rcases hH with h1 | h1
      · exact Or.inl h1
      · have := hzO hc; simp only [win, outside_cons, outside_nil, and_true] at this
        exact Or.inr ⟨h1, this⟩
    · refine ⟨?_, ?_⟩
      · rcases hzH with h1 | h1
        · have := hap.apart_of_inRanges h1; unfold Apart; omega
        · exact (hin.apart h1).symm
      · rcases hH with h1 | h1
        · exact Or.inl h1
        · obtain ⟨r, hr, a1, a2⟩ := hin
          have := MemFrame.outside_mem h1 hr
          omega
  -- reads of `Mw` inside `z`'s header and inside the result array
  have rdW : ∀ a n, zA ≤ a → a + n ≤ zA + 32 → Mw.readLE a n = (hdrW M zA l c).readLE a n := by
    intro a n h1 h2
    rcases hzH1 with hi | ho
    · exact hLw.readLE_nil a n (hi.sub h1 h2)
    · exact hMw.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.of_sub h1 h2, by omega⟩)
  have rdA : 0 < c → ∀ a n, p ≤ a → a + n ≤ p + 8 * c → s'.mem.readLE a n = M.readLE a n := by
    intro hc a n h1 h2
    obtain ⟨hap, hor⟩ := harr hc
    unfold Apart at hap
    rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show Mw.readLE a n = (hdrW M zA l c).readLE a n from ?_]
    · simp only [hdrW]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rcases hor with hi | ⟨ho, hw⟩
    · exact hLw.readLE_nil a n (hi.sub h1 h2)
    · exact hMw.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.of_sub h1 h2, by omega⟩)
  have eN : s'.mem.readLE zA 1 = 0 := by rw [hm, Janus.Arm64.Memory.readLE_writeLE_self]
  have eP : s'.mem.readLE (zA + 8) 8 = p := by
    rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eL : s'.mem.readLE (zA + 16) 8 = l := by
    rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega)]
    simp only [hdrW]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eC : s'.mem.readLE (zA + 24) 8 = c := by
    rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega)]
    simp only [hdrW]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eV : natVal s'.mem p l = V := by
    rw [← hA.val]
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0; rfl
    · exact rdA (by omega) _ _ (Nat.le_refl _) (by omega)
  have eNorm : NatNorm s'.mem p l := by
    rcases hA.norm with h1 | h1
    · exact Or.inl h1
    · rcases Nat.eq_zero_or_pos l with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rw [rdA (by omega) _ _ (by omega) (by omega)]; exact h1)
  have hacc : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := by
    intro a n w
    rw [hm, Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE, hMw.accessible]
    simp only [hdrW, Janus.Arm64.Memory.accessible_writeLE]
  -- frames
  have hFH : MemFrame M (hdrW M zA l c) [(zA, zA + 32)] := by simp only [hdrW]; janus_frame
  have hF2 : MemFrame Mw ((Mw.writeLE (zA + 8) 8 p).writeLE zA 1 0) [(zA, zA + 32)] := by janus_frame
  rw [← hm] at hF2
  refine ⟨⟨?_, L', b', hA.ext, hA.bud, ?_, ⟨?_, hz8, hz48, ?_, hzH1, ?_, ?_, ?_, ?_, by rw [eC]; exact hc40⟩, ?_, ?_, ?_⟩, by rw [eC]; exact hc40⟩
  · simp only [RunIface.IntV]; rw [eP, eL, eV]
  · rw [hm, view_writeLE_held (hzH1.sub (by omega) (by omega)), view_writeLE_held (hzH1.sub (by omega) (by omega))]
    exact hIw
  · exact eN
  · rw [hacc]; rw [hA.mf.accessible]; exact hzacc
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
    obtain ⟨k1, k2, k3⟩ := out_post h0x1138 ho
    rw [MemFrame.byte hF2 k1, MemFrame.byte hMw k2, MemFrame.byte hFH k1]
    exact MemFrame.byte hA.mf k3
  · rw [← zarr_eq]
    refine LiveFrame.of_bytes fun a hin ho => ?_
    rw [outside_cons] at ho
    obtain ⟨hoZ, hoA⟩ := ho
    have k1 : Outside a 1 [(zA, zA + 32)] := by rw [outside_cons]; exact ⟨hoZ, trivial⟩
    rw [MemFrame.byte hF2 k1, LiveFrame.byte hLw (hA.ext.inRanges_old hin) trivial, MemFrame.byte hFH k1]
    exact LiveFrame.byte hA.lf hin hoA

end FvModexp.Amd64.IExp
