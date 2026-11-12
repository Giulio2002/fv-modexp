import FvModexp.Proofs.Arm64.Exp.IExpP
import FvModexp.Proofs.Arm64.Exp.IExpD
import FvModexp.Proofs.Common.ByteFrame

/-!
# `(*Int).exp` (arm64): from `nat.expNN`'s postcondition to `RunIface.IntPost` (pure)

* `AtN`: the facts at `expNN`'s return (memory `M`): the result `(p, l, c)` (`p` the register value, i.e. below
  `2^64`; an empty result's pointer is irrelevant) holds `V = x^y mod m`, normalised, cap
  `< 2^40`, live in `L'`, the old array of `z` or a fresh one; `M` differs from the entry memory only in `R.rt`, the
  window and `z`'s old array (frames at byte granularity: a nil `z` has an empty, arbitrarily placed array).
* `atN_of`: `AtN` from `ExpSpec`'s precondition, the frame of segments A-C and `ExpN.PostNil`.
* `post_of`: `AtN` and segment D's continuation facts (`runD`'s `KF`) give `IntPost` and the result's cap bound.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option autoImplicit false

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntOK IntPre IntPost IntV arrW)

/-- the facts at `expNN`'s return (memory `M`; result `(p, l, c)` holding `V`, live set `L'`, budget `b'`) -/
structure AtN (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (stk above : Nat) (s : State) (zA V p l c b' : Nat)
    (L' : List (Nat × Nat)) (M : Memory) : Prop where
  val : natVal M p l = V
  norm : NatNorm M p l
  lc : l ≤ c
  c40 : c < 2 ^ 40
  p64 : p < 2 ^ 64
  ext : LiveExt R L L'
  bud : b - B ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  live : NatLive M R L' p c
  orf : c = 0 ∨ (p = s.mem.readLE (zA + 8) 8 ∧ c = s.mem.readLE (zA + 24) 8) ∨
    (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s stk above ++ arrW s.mem zA)
  lf : LiveFrame s.mem M L (arrW s.mem zA)

/-- an operand's value survives a frame that misses its array -/
theorem natVal_eq0 {m M : Memory} {p l c lo hi : Nat} (hlc : l ≤ c)
    (hout : 0 < c → Outside p (8 * c) [(lo, hi)]) (hF : MemFrame m M [(lo, hi)]) : natVal M p l = natVal m p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; rfl
  · have := hout (by omega)
    exact hF.readLE _ _ (this.of_sub (Nat.le_refl _) (by omega))

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`AtN`** at `expNN`'s return, from `ExpSpec`'s precondition, the frame of segments A-C and `PostNil` -/
theorem atN_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above K : Nat}
    {costF : Nat → Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (hK : K + 1632 ≤ stk) (hab : 48 ≤ above)
    {zp zl zc yp yl mp n : Nat}
    (ez8 : s.mem.readLE (zA + 8) 8 = zp) (ez16 : s.mem.readLE (zA + 16) 8 = zl)
    (ez24 : s.mem.readLE (zA + 24) 8 = zc)
    (ey8 : s.mem.readLE (yA + 8) 8 = yp) (ey16 : s.mem.readLE (yA + 16) 8 = yl)
    (em8 : s.mem.readLE (mA + 8) 8 = mp) (em16 : s.mem.readLE (mA + 16) 8 = n)
    (hcost : 24 + ExpN.NCost costF costR costS costP zl yl n 0 (Nat.log2 (natVal s.mem mp n)) ≤ B)
    {S3 S4 : State} (hsp3 : S3.sp = BitVec.ofNat 64 (s.sp.toNat - 320)) (h28 : S3.regs 28 = s.regs 28)
    (hF3 : MemFrame s.mem S3.mem [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)])
    (hpost : ExpN.PostNil R b L K costF costR costS costP zp zc zp zl yp yl mp n S3 S4) :
    ∃ p l c b' L', S4.regs 0 = BitVec.ofNat 64 p ∧ S4.regs 1 = BitVec.ofNat 64 l ∧ S4.regs 2 = BitVec.ofNat 64 c ∧
      AtN R b B L stk above s zA (IntV s.mem zA ^ IntV s.mem yA % IntV s.mem mA) p l c b' L' S4.mem := by
  obtain ⟨⟨-, ⟨-, hstk, -, -⟩, -, hrt, -, -, hLs, -⟩, -, -, -, -, hops, -⟩ := hpre
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  have hom := hops mA (by simp)
  clear hops
  obtain ⟨⟨-, -, -, -, -, hzL, hzlc, -, -⟩, -, hzO, -, -⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, -, hylc, -, -⟩, -, hyO, -, -⟩ := hoy
  obtain ⟨⟨-, -, -, -, -, -, hmlc, -, -⟩, -, hmO, -, -⟩ := hom
  obtain ⟨p, l, c, h0, h1, h2, hv, hnm, hlc, hc40, L', b', hx, hb, hinv, hnl, hd, hMF, hLF⟩ := hpost
  have hst : stk ≤ s.sp.toNat := hstk
  have hS3 : S3.sp.toNat = s.sp.toNat - 320 := by rw [hsp3, BitVec.toNat_ofNat]; omega
  have hF3w : MemFrame s.mem S3.mem [(s.sp.toNat - 328, s.sp.toNat + 48)] :=
    hF3.mono fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hvw : ∀ {a q k : Nat}, s.mem.readLE (a + 8) 8 = q → s.mem.readLE (a + 16) 8 = k →
      k ≤ s.mem.readLE (a + 24) 8 →
      (0 < s.mem.readLE (a + 24) 8 → Outside (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8)
        (win s stk above)) → natVal S3.mem q k = natVal s.mem q k := by
    intro a q k e8 e16 hlc' hO
    subst e8
    exact natVal_eq0 hlc' (fun h => by
      have := hO h; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega) hF3w
  have evz := hvw ez8 ez16 (ez16 ▸ hzlc) hzO
  have evy := hvw ey8 ey16 (ey16 ▸ hylc) hyO
  have evm := hvw em8 em16 (em16 ▸ hmlc) hmO
  rw [evz, evy, evm] at hv
  rw [evm] at hb
  have hpp : 0 < c → p % 2 ^ 64 = p := fun hc => Nat.mod_eq_of_lt (by have := (hnl hc).2.2.2; omega)
  have hpe : BitVec.ofNat 64 (p % 2 ^ 64) = BitVec.ofNat 64 p := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]
  refine ⟨p % 2 ^ 64, l, c, b', L', h0.trans hpe.symm, h1, h2, ⟨?_, ?_, hlc, hc40, Nat.mod_lt _ (by omega), hx,
    by omega, by rw [← h28]; exact hinv, ?_, ?_, ?_, ?_⟩⟩
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp only [RunIface.IntV]; rw [ez8, ez16, ey8, ey16, em8, em16]
      simp only [natVal_zero] at hv ⊢; exact hv
    · rw [hpp (by omega)]; simp only [RunIface.IntV]; rw [ez8, ez16, ey8, ey16, em8, em16]; exact hv
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · exact Or.inl hl
    · rw [hpp (by omega)]; exact hnm
  · intro hc; rw [hpp hc]; exact hnl hc
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · exact Or.inl hc
    · rw [hpp hc, ez8, ez24]
      rcases hd with ⟨h, -⟩ | h | h
      · omega
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · -- memory frame, byte by byte
    refine MemFrame.of_bytes (fun a ho => ?_) (fun a k w => by rw [hMF.accessible, hF3.accessible])
    have hzrng : ∀ a, Outside a 1 (arrW s.mem zA) → Outside a 1 [(zp, zp + 8 * zc)] := fun a h => by
      simp only [arrW, ez8, ez24] at h
      split at h
      · exact h
      · rename_i hz; have : zc = 0 := by omega
        subst this; exact outside1_empty a zp
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hoR, hoW⟩, hoA⟩ := ho
    have h3 := hzrng a hoA
    simp only [winA, outside_cons, outside_nil, and_true] at hoW
    rw [MemFrame.byte hMF (by
      simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h3 ⊢
      rw [hS3]; exact ⟨⟨hoR, by omega, by omega⟩, h3⟩)]
    exact MemFrame.byte hF3 (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine LiveFrame.of_bytes fun a hin ho => ?_
    have hzrng : Outside a 1 [(zp, zp + 8 * zc)] := by
      simp only [arrW, ez8, ez24] at ho
      split at ho
      · exact ho
      · rename_i hz; have : zc = 0 := by omega
        subst this; exact outside1_empty a zp
    rw [LiveFrame.byte hLF hin hzrng]
    obtain ⟨r, hr, e1, e2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this
    exact MemFrame.byte hF3 (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`IntPost`** (and the result's cap bound) from `AtN` and segment D's continuation facts: `Mw` the memory after
the header stores `len, cap` and (barrier on) the buffer stores, the final stores `z.abs.ptr = p`, `z.neg = 0` -/
theorem post_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above : Nat} {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (h4416 : 4416 ≤ stk) (hab : 48 ≤ above)
    {V p l c b' : Nat} {L' : List (Nat × Nat)} {M : Memory}
    (hA : AtN R b B L stk above s zA V p l c b' L' M) {Mw : Memory}
    (hMw : MemFrame (hdrW M zA l c) Mw (R.rt ++ [(s.sp.toNat - 4416, s.sp.toNat - 328)]))
    (hLw : LiveFrame (hdrW M zA l c) Mw L' [])
    (hIw : R.inv b' L' (s.regs 28).toNat (view R.rt L' Mw))
    (s' : State) (hm : s'.mem = (Mw.writeLE (zA + 8) 8 p).writeLE zA 1 0) :
    IntPost R b B L stk above zA V s s' ∧ s'.mem.readLE (zA + 24) 8 < 2 ^ 40 := by
  obtain ⟨⟨-, ⟨-, hstk, -, -⟩, -, hrt, -, -, -, -⟩, -, -, -, -, hops, -⟩ := hpre
  obtain ⟨⟨-, hz8, hz48, hzacc, hzH, -, -, -, hzap⟩, hzW, hzO, -, -⟩ := hops zA (by simp)
  clear hops
  have hst : stk ≤ s.sp.toNat := hstk
  have hzH1 : Held R L' zA 32 := hA.ext.held hzH
  have hc40 := hA.c40; have hlc := hA.lc; have hp64 := hA.p64
  simp only [win, outside_cons, outside_nil, and_true] at hzW
  -- the result array: apart from `z`'s header, held, outside the stack window
  have harr : 0 < c → Apart p (8 * c) zA 32 ∧ (InRanges p (8 * c) L' ∨
      (Outside p (8 * c) R.rt ∧ (p + 8 * c ≤ s.sp.toNat - stk ∨ s.sp.toNat + above ≤ p))) := by
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
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show Mw.readLE a n = (hdrW M zA l c).readLE a n from ?_]
    · simp only [hdrW]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rcases hor with hi | ⟨ho, hw⟩
    · exact hLw.readLE_nil a n (hi.sub h1 h2)
    · exact hMw.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.of_sub h1 h2, by omega⟩)
  have eN : s'.mem.readLE zA 1 = 0 := by rw [hm, Memory.readLE_writeLE_self]
  have eP : s'.mem.readLE (zA + 8) 8 = p := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eL : s'.mem.readLE (zA + 16) 8 = l := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega)]
    simp only [hdrW]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have eC : s'.mem.readLE (zA + 24) 8 = c := by
    rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      rdW _ _ (by omega) (by omega)]
    simp only [hdrW]
    rw [Memory.readLE_writeLE_self]
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
    rw [hm, Memory.accessible_writeLE, Memory.accessible_writeLE, hMw.accessible]
    simp only [hdrW, Memory.accessible_writeLE]
  -- frames
  have hFH : MemFrame M (hdrW M zA l c) [(zA, zA + 32)] := by simp only [hdrW]; janus_frame
  have hF2 : MemFrame Mw ((Mw.writeLE (zA + 8) 8 p).writeLE zA 1 0) [(zA, zA + 32)] := by janus_frame
  rw [← hm] at hF2
  refine ⟨⟨?_, L', b', hA.ext, hA.bud, ?_, ⟨?_, hz8, hz48, ?_, hzH1, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, by rw [eC]; exact hc40⟩
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
    refine MemFrame.of_bytes (fun a ho => ?_) (fun a k w => by rw [hacc, hA.mf.accessible])
    rw [outside_append, outside_append, outside_cons] at ho
    obtain ⟨⟨hoR, hoW⟩, hoZ, hoA⟩ := ho
    have hoW' := hoW
    simp only [winA, outside_cons, outside_nil, and_true] at hoW'
    rw [MemFrame.byte hF2 (by simp only [outside_cons, outside_nil, and_true]; omega),
      MemFrame.byte hMw (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hoR, by omega⟩),
      MemFrame.byte hFH (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact MemFrame.byte hA.mf (by rw [outside_append, outside_append]; exact ⟨⟨hoR, hoW⟩, hoA⟩)
  · refine LiveFrame.of_bytes fun a hin ho => ?_
    simp only [outside_cons] at ho
    obtain ⟨hoZ, hoA⟩ := ho
    rw [MemFrame.byte hF2 (by simp only [outside_cons, outside_nil, and_true]; omega),
      LiveFrame.byte hLw (hA.ext.inRanges_old hin) (by simp),
      MemFrame.byte hFH (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact LiveFrame.byte hA.lf hin hoA

end FvModexp.Arm64.IExp
