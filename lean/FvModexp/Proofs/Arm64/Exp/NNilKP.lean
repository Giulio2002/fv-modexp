import FvModexp.Proofs.Arm64.Exp.NNilP
import FvModexp.Proofs.Arm64.Exp.NFree
import FvModexp.Proofs.Arm64.Exp.NEpi

/-!
# `nat.expNN` (arm64), `stk == nil`: the pure facts of the flag-1 epilogue (no machine run)

* `NewStk.outWs` / `NewStk.outL`: the new stack's write ranges (`stkWs`, the header's `len` word) are outside anything
  outside `R.rt` / inside `L` (header and array are fresh runtime objects; an empty array is `(0, 0)`).
* `stkOK_frame`: `StkOK` and the header words survive a frame that keeps the header.
* `liveSep_ext`: a `LiveExt` of a live set outside a window apart from `R.rt` is outside it.
* `freePre`: `FreeSh.Pre` (the deferred `stk.free()` closure's context) at its entry state.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

section
variable {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g : Nat} {M1 : Memory} {st : Nat}

theorem NewStk.outWs (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : Outside a k R.rt) :
    Outside a k (stkWs M1 st) := by
  have hl : stLen M1 st = 0 := hN.2.2.2.2.2.2.1
  have hc0 : stCap M1 st = 0 → stW M1 st = 0 := hN.2.2.2.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := hN.out h
  simp only [stkWs, hl, Nat.mul_zero, Nat.add_zero]
  simp only [outside_cons, outside_nil, and_true] at h1 ⊢
  refine ⟨h1, ?_⟩
  rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
  · have := hc0 hc; simp only [stW, stCap] at this hc ⊢; rw [this, hc]; omega
  · have := h2 hc; simp only [outside_cons, outside_nil, and_true] at this; exact this

theorem NewStk.outL (hN : NewStk R L L1 b b1 g M1 st) {a k : Nat} (h : InRanges a k L) :
    Outside a k (stkWs M1 st) ∧ Outside a k [(st + 8, st + 16)] := by
  have hl : stLen M1 st = 0 := hN.2.2.2.2.2.2.1
  have hc0 : stCap M1 st = 0 → stW M1 st = 0 := hN.2.2.2.2.2.2.2.2.1
  have hh := apart_fresh (Or.inl h) hN.hdr.2 hN.hdr.1
  simp only [stkWs, hl, Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
  refine ⟨⟨hh, ?_⟩, by omega⟩
  rcases Nat.eq_zero_or_pos (stCap M1 st) with hc | hc
  · have := hc0 hc; simp only [stW, stCap] at this hc ⊢; rw [this, hc]; omega
  · exact apart_fresh (Or.inl h) (hN.arr hc).2 (hN.arr hc).1
end

theorem stkOK_frame {R : RtInv} {L : List (Nat × Nat)} {st : Nat} {m m' : Memory} {ws : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' ws) (ho : Outside st 24 ws) :
    StkOK m' R L st ∧ stW m' st = stW m st ∧ stLen m' st = stLen m st ∧ stCap m' st = stCap m st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have ew : stW m' st = stW m st := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have el : stLen m' st = stLen m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have ec : stCap m' st = stCap m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  refine ⟨⟨h1, h2, by rw [hF.accessible]; exact h3, h4, ?_, by rw [el, ec]; exact h6, by rw [ec]; exact h7⟩,
    ew, el, ec⟩
  rw [ew, ec]; intro hc
  obtain ⟨a1, a2, a3, a4⟩ := h5 hc
  exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩

theorem stkRs_congr {m m' : Memory} {st : Nat} (hw : stW m' st = stW m st) (hc : stCap m' st = stCap m st) :
    stkRs m' st = stkRs m st := by
  simp only [stkRs]; rw [hw, hc]

theorem liveSep_ext {R : RtInv} {L1 L2 w : List (Nat × Nat)} (hx : LiveExt R L1 L2) (hL : LiveSep L1 w)
    (hw : ∀ r ∈ w, Outside r.1 (r.2 - r.1) R.rt) : LiveSep L2 w := by
  obtain ⟨ns, rfl, hn, -⟩ := hx
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hL r hr
  · refine outside_of_forall fun q hq => ?_
    have := out_inR2 (hw q hq) (hn r hr).1
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closure's context at its entry `S` (`SP = sp + 1056`, `X26` = the closure record `sp + 1272`) -/
theorem freePre {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b' g sp K st r : Nat} {M1 : Memory} {S : State}
    (hN : NewStk R L L1 b b1 g M1 st) (hr : RetPt r)
    (hsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h26 : S.regs 26 = BitVec.ofNat 64 (sp + 1272))
    (h30 : S.regs 30 = BitVec.ofNat 64 (r + 32)) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible (g + 16) 8 false = true) (hg3 : S.mem.readLE (g + 16) 8 + K < sp)
    (hgo : Outside (g + 16) 8 ((sp - K, sp + 1432) :: R.rt)) (hal : sp % 16 = 0) (hK4 : 4304 ≤ K) (hKs : K ≤ sp)
    (hsp2 : sp + 1432 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp - K) (K + 1432) true = true)
    (hwrt : LiveSep [(sp - K, sp + 1432)] R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (h1280 : S.mem.readLE (sp + 1280) 8 = st) (hok : StkOK S.mem R L2 st) (hlen : stLen S.mem st = 0)
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0)
    (hdis : 0 < stCap S.mem st → Apart st 24 (stW S.mem st) (8 * stCap S.mem st))
    (hrs : ∀ x ∈ stkRs S.mem st, x ∈ L2) (hx : LiveExt R L1 L2)
    (hput : R.ok (cA "sync.(*Pool).Put") [Free.poolA]) (hinv : R.inv b' L2 g (view R.rt L2 S.mem)) :
    FreeSh.Pre R b' L2 (stkRs S.mem st) S := by
  have hst0 : 0 < st := hN.2.2.1
  have e28 : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have esp : S.sp.toNat = sp + 1056 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have e26 : (S.regs 26).toNat = sp + 1272 := by rw [h26, BitVec.toNat_ofNat]; omega
  have hr' : r < 2 ^ 40 ∧ (r + 32) % 4 = 0 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have e30 : (S.regs 30).toNat = r + 32 := by rw [h30, BitVec.toNat_ofNat]; omega
  have hso : Free.stkOf S = st := by
    show S.mem.readLE ((S.regs 26).toNat + 8) 8 = st
    rw [e26, show sp + 1272 + 8 = sp + 1280 by omega]; exact h1280
  have hwout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  have hhd := hN.hdr.1
  have hsh := StkSh.of_ok hok hst0 hlen hc0 hdis
  simp only [outside_cons] at hgo
  obtain ⟨hgo1, hgo2⟩ := hgo
  have hhg := out_inR2 hgo2 hhd
  have hhw := out_inR2 hwout hhd
  have hGd : GuardOK S 4144 := by
    unfold GuardOK; rw [e28, esp]; exact ⟨hg1, hg2, by omega⟩
  have hSo : StackOK S 4144 0 := by
    unfold StackOK; rw [esp]
    exact ⟨by omega, by omega, by omega, Memory.accessible_mono _ hacc (by omega) (by omega)⟩
  unfold FreeSh.Pre
  rw [hso, e28, esp, e26, e30]
  refine ⟨hGd, hSo, hr'.2, by omega, by omega, Memory.accessible_mono _ (Memory.accessible_read_of_write _ hacc) (by omega) (by omega),
    by unfold Apart; omega, hsh.1, hsh.2.2, by unfold Apart; omega, by unfold Apart; omega,
    by unfold Apart; omega, hgo2, hrs, hput, hinv, ?_, hwout.of_sub (by omega) (by omega)⟩
  refine LiveSep.sub_win (lo := sp - K) (hi := sp + 1432) ?_ (by omega) (by omega)
  refine liveSep_ext hx (hN.liveSep hLs fun q hq => ?_) fun q hq => ?_
  all_goals
    simp only [List.mem_singleton] at hq; subst hq; simp only
    rwa [show sp + 1432 - (sp - K) = K + 1432 by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `stk == nil` post** from the stack-given `Post` at the virtual entry (`{s with mem := M1}`, memory `M2` at
the callee's return) and the frames of the epilogue's `stk.free()` (`M2 → m4`: `R.rt`, the window, the header's `len`
word; live set `dropAll L2 (stkRs M2 st)`) -/
theorem postNil_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L [])
    {M2 m4 : Memory} {p l c b' : Nat} {L2 : List (Nat × Nat)}
    (hv : natVal M2 p l = natVal M1 xp xl ^ natVal M1 yp yl % natVal M1 mp n) (hnm : NatNorm M2 p l)
    (hlc : l ≤ c) (hc64 : c < 2 ^ 64) (hx : LiveExt R L1 L2)
    (hb : b1 - NCost costF costR costS costP xl yl n (stLen M1 st) (Nat.log2 (natVal M1 mp n)) ≤ b')
    (hnl : NatLive M2 R L2 p c)
    (hd : c = 0 ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L1))
    (hsb : StackBackL R L1 L2 st M1 M2)
    (hMF : MemFrame M1 M2 (R.rt ++ winA { s with mem := M1 } (K + 1312) 120 ++ [(zp, zp + 8 * zc)] ++ stkWs M1 st))
    (hLF2 : LiveFrame M1 M2 L1 ([(zp, zp + 8 * zc)] ++ stkWs M1 st)) (hrs : ResSep M1 M2 st p c)
    (hF4 : MemFrame M2 m4 (R.rt ++ wN sp K ++ [(st + 8, st + 16)])) (hLF4 : LiveFrame M2 m4 L2 [(st + 8, st + 16)])
    (hinv4 : R.inv b' (dropAll L2 (stkRs M2 st)) g (view R.rt (dropAll L2 (stkRs M2 st)) m4))
    (s' : State) (hm' : s'.mem = m4) (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h1 : s'.regs 1 = BitVec.ofNat 64 l)
    (h2 : s'.regs 2 = BitVec.ofNat 64 c) :
    PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s' := by
  subst hm'
  obtain ⟨⟨hs1, hs28, hg1, -, -, -, -, -, hKs, hsp2, -, hwrt, hLs, -, -⟩, -, -, -, -, -,
    -, -, -, -, hmO, -, -, hmN, hyO, -, -, hyN, -, -, hxO, -, -, hxN, -, -, -,
    -, -, -, ⟨-, hzN⟩, -⟩ := hP
  obtain ⟨hL1, hrs0, -, -, -, -, hl0, -, -, -, -, -, hdis0, hbb, -, -⟩ := id hN
  have esp : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have e28 : (s.regs 28).toNat = g := by rw [hs28, BitVec.toNat_ofNat]; omega
  have hwout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  have ex := (opnd_v hxO hLF hF hxN).1
  have ey := (opnd_v hyO hLF hF hyN).1
  have em := (opnd_v hmO hLF hF hmN).1
  rw [ex, ey, em] at hv
  rw [em, hl0] at hb
  have hmA : 0 < stCap M1 st → (stW M1 st, stW M1 st + 8 * stCap M1 st) ∈ L1 := fun hc => by
    rw [hL1]; refine List.mem_append_right _ ?_
    simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, true_or, or_true]
  have hmH : (st, st + 24) ∈ L1 := by rw [hL1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- the result's range: held, outside the window and the header's `len` word, apart from the final stack ranges
  have hres : 0 < c → Held R L2 p (8 * c) ∧ Outside p (8 * c) (wN sp K) ∧ Outside p (8 * c) [(st + 8, st + 16)] ∧
      ∀ q ∈ stkRs M2 st, Apart p (8 * c) q.1 (q.2 - q.1) := by
    intro hc
    have key : Apart p (8 * c) (sp - K) (K + 1432) ∧ Apart p (8 * c) st 24 ∧
        (0 < stCap M1 st → Apart p (8 * c) (stW M1 st) (8 * stCap M1 st)) := by
      rcases hd with h | ⟨rfl, rfl⟩ | ⟨hin, hap⟩
      · omega
      · obtain ⟨hz1, hz2⟩ := hzN hc
        exact ⟨hz2, (hN.apart hz1).1, fun hc' => apart_fresh hz1 (hN.arr hc').2 (hN.arr hc').1⟩
      · refine ⟨(hin.apart hwout).symm, ?_, fun hc' => ?_⟩
        · simpa only [Nat.add_sub_cancel_left] using hap _ hmH
        · simpa only [Nat.add_sub_cancel_left] using hap _ (hmA hc')
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨(hnl hc).2.1, ?_, ?_, stkRs_forall (P := fun q => Apart p (8 * c) q.1 (q.2 - q.1)) ?_ fun hc2 => ?_⟩
    · unfold Apart at k1; simp only [wN, outside_cons, outside_nil, and_true]; omega
    · unfold Apart at k2; simp only [outside_cons, outside_nil, and_true]; omega
    · simpa only [Nat.add_sub_cancel_left] using k2
    · simp only [Nat.add_sub_cancel_left]
      by_cases hk : stW M2 st = stW M1 st ∧ stCap M2 st = stCap M1 st
      · rw [hk.1, hk.2]; exact k3 (by rw [← hk.2]; exact hc2)
      · exact hrs hc hk
  -- the live set after the `Put`
  have hp0 : (stkRs M1 st).Pairwise fun a b => Apart a.1 (a.2 - a.1) b.1 (b.2 - b.1) := by
    simp only [stkRs]
    split
    · exact List.pairwise_singleton _ _
    · refine List.Pairwise.cons (fun q hq => ?_) (List.pairwise_singleton _ _)
      simp only [List.mem_singleton] at hq; subst hq
      simpa only [Nat.add_sub_cancel_left] using hdis0
  have hFr : ∀ q ∈ stkRs M2 st, q ∉ L := stkRs_forall (P := fun q => q ∉ L)
    (not_mem_of_apartAll (by simp only; omega) (by simpa only [Nat.add_sub_cancel_left] using hN.hdr.2))
    fun hc2 => by
      rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨-, hap⟩
      · rw [ew, ec]
        have hc' : 0 < stCap M1 st := by rw [← ec]; exact hc2
        exact not_mem_of_apartAll (by simp only; omega) (by simpa only [Nat.add_sub_cancel_left] using (hN.arr hc').2)
      · exact not_mem_of_apartAll (by simp only; omega)
          (by simpa only [Nat.add_sub_cancel_left] using (show ApartAll _ _ L from fun q hq => hap q (hN.mem hq)))
  have hLE : LiveExt R L (dropAll L2 (stkRs M2 st)) := liveExt_dropAll hrs0 hp0 (by rw [← hL1]; exact hx) hFr
  -- reads of the result
  have hrd : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → 0 < c → s'.mem.readLE a k = M2.readLE a k := by
    intro a k h1 h2 hc
    obtain ⟨hH, hw, hh, -⟩ := hres hc
    exact Expmc.held_readLE (hH.sub h1 h2) hF4 hLF4 (hw.of_sub h1 h2) (hh.of_sub h1 h2)
  -- frames
  have hFz : MemFrame s.mem s'.mem (R.rt ++ winA s (K + 1312) 120 ++ [(zp, zp + 8 * zc)]) := by
    refine ⟨fun a k ho => ?_, fun a k w => by rw [hF4.accessible, hMF.accessible, hF.accessible]⟩
    simp only [outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    have hw : Outside a k (wN sp K) := by
      simp only [winA, esp, wN, outside_cons, outside_nil, and_true] at hwa ⊢; omega
    have hws := hN.outWs hrt
    have hhd : Outside a k [(st + 8, st + 16)] := by
      have := (hN.out hrt).1; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    have hwa' : Outside a k (winA { s with mem := M1 } (K + 1312) 120) := hwa
    rw [hF4.readLE a k (by simp only [outside_append]; exact ⟨⟨hrt, hw⟩, hhd⟩),
      hMF.readLE a k (by simp only [outside_append]; exact ⟨⟨⟨hrt, hwa'⟩, hz⟩, hws⟩),
      hF.readLE a k (by simp only [outside_append]; exact ⟨hrt, hw⟩)]
  have hLz : LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)] := ⟨fun a k hin hz => by
    obtain ⟨hws, hhd⟩ := hN.outL hin
    have hin1 : InRanges a k L1 := hin.of_subset fun _ hr => hN.mem hr
    rw [hLF4.readLE a k (hx.inRanges_old hin1) hhd,
      hLF2.readLE a k hin1 (by simp only [outside_append]; exact ⟨hz, hws⟩), hLF.readLE_nil a k hin]⟩
  refine ⟨p, l, c, h0, h1, h2, ?_, ?_, hlc, hc64, dropAll L2 (stkRs M2 st), b', hLE, by omega, ?_, ?_, ?_, hFz, hLz⟩
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp only [natVal, Nat.mul_zero, Memory.readLE_zero] at hv ⊢; exact hv
    · rw [← hv]; exact hrd p (8 * l) (Nat.le_refl _) (by omega) (by omega)
  · rcases hnm with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos l with hl | hl
      · exact Or.inl hl
      · right; rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h
  · rw [e28]; exact hinv4
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc
    exact ⟨a1, held_dropAll a2 (by omega) (hres hc).2.2.2, by rw [hF4.accessible]; exact a3, a4⟩
  · exact hd.imp_right (Or.imp_right fun ⟨hin, hap⟩ => ⟨hin, fun q hq => hap q (hN.mem hq)⟩)

end FvModexp.Arm64.ExpN
