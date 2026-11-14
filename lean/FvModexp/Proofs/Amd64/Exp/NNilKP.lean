import FvModexp.Proofs.Amd64.Exp.NNilV
import FvModexp.Proofs.Amd64.Exp.NFree

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the pure facts of the flag-1 epilogue (no machine run) (agent expmc s75; twin
of `Arm64.ExpN` NNilKP)

`sp = t - 0x498` (`t` = the entry `RSP`), window `[sp - K, sp + 0x510)`.
* `opnd_v0`: `opnd_v` for an operand whose facts are stated only for a positive length.
* `freePreE`: `Free.PreS` (the deferred `stk.free()` closure's context, `StkSh` shape) at the closure's entry
  (`RSP = t - 0x110 = sp + 0x388`, `RDX = t - 0x30 = sp + 0x468`, stack word `[t - 0x28] = [sp + 0x470]`); template
  top's `Q.NatDiv.freePreM`.
* `postNil_of`: the stack-given `Post` at the virtual entry `{s with mem := M1}` and the frames of the closure give
  `PostNil` at the real entry `s`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
  FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

theorem opnd_v0 {R : RtInv} {L : List (Nat × Nat)} {sp K p k : Nat} {M M1 : Janus.Arm64.Memory}
    (h : 0 < k → NE0 R L sp K p (8 * k)) (hLF : LiveFrame M M1 L []) (hF : MemFrame M M1 (R.rt ++ wN sp K))
    (hN : NatNorm M p k) : natVal M1 p k = natVal M p k ∧ NatNorm M1 p k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; exact ⟨by simp only [natVal, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero], Or.inl rfl⟩
  · exact opnd_v (h hk0) hLF hF hN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closure's context at its entry `S` (`RSP = sp + 0x388`, `RDX = sp + 0x468`) -/
theorem freePreE {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b' g sp K st : Nat} {M1 : Janus.Arm64.Memory}
    {S : State} (hN : NewStk R L L1 b b1 g M1 st)
    (hsp : (S.regs 4).toNat = sp + 0x388) (h2 : (S.regs 2).toNat = sp + 0x468)
    (hra : S.mem.readLE (sp + 0x388) 8 < 2 ^ 47) (h14 : (S.regs 14).toNat = g)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible (g + 16) 8 false = true)
    (hg3 : S.mem.readLE (g + 16) 8 + K < sp)
    (hgo1 : Apart (g + 16) 8 (sp - K) (K + 0x510)) (hgo2 : Outside (g + 16) 8 R.rt)
    (hal : sp % 8 = 0) (hK4 : 4136 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 0x510 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp - K) (K + 0x510) true = true)
    (hwout : Outside (sp - K) (K + 0x510) R.rt) (hLs : LiveSep L [(sp - K, sp + 0x510)])
    (h24 : S.mem.readLE (sp + 0x470) 8 = st) (hok : StkOK S.mem R L2 st) (hlen : stLen S.mem st = 0)
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0)
    (hdis : 0 < stCap S.mem st → Apart st 24 (stW S.mem st) (8 * stCap S.mem st))
    (hrs : ∀ x ∈ stkRs S.mem st, x ∈ L2) (hx : LiveExt R L1 L2)
    (hput : R.ok (cA "sync.(*Pool).Put") [Free.poolA]) (hinv : R.inv b' L2 g (view R.rt L2 S.mem)) :
    Free.PreS R b' L2 (stkRs S.mem st) S := by
  have hst0 : 0 < st := hN.2.2.1
  have hso : Free.stkOf S = st := by
    show S.mem.readLE ((S.regs 2).toNat + 8) 8 = st
    rw [h2, show sp + 0x468 + 8 = sp + 0x470 by omega]; exact h24
  have hhd := hN.hdr.1
  have hsh := StkSh.of_ok hok hst0 hlen hc0 hdis
  have hhg := out_inR2 hgo2 hhd
  have hhw := out_inR2 hwout hhd
  unfold Apart at hgo1
  unfold Free.PreS Free.Pre
  rw [hso, h14, hsp, h2]
  refine ⟨⟨hg1, hg2, by omega, by omega, by omega,
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega), hra, by omega,
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hacc) (by omega) (by omega),
    by unfold Apart; omega, hsh.1, by unfold Apart; omega, by unfold Apart; omega,
    by unfold Apart; omega, hgo2, hrs, hput, hinv, ?_, hwout.of_sub (by omega) (by omega)⟩, hsh.2.2⟩
  refine LiveSep.sub_win (lo := sp - K) (hi := sp + 0x510) ?_ (by omega) (by omega)
  refine liveSep_ext hx (hN.liveSep hLs fun q hq => ?_) fun q hq => ?_
  all_goals
    simp only [List.mem_singleton] at hq; subst hq; simp only
    rwa [show sp + 0x510 - (sp - K) = K + 0x510 by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the `stk == nil` post** from the stack-given `Post` at the virtual entry (`{s with mem := M1}`, memory `M2` at
the callee's return) and the frames of the epilogue's `stk.free()` (`M2 → m4`: `R.rt`, the window, the header's `len`
word; live set `dropAll L2 (stkRs M2 st)`) -/
theorem postNil_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costD : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hx0 : xl ≠ 0)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Janus.Arm64.Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L [])
    {M2 m4 : Janus.Arm64.Memory} {p l c b' : Nat} {L2 : List (Nat × Nat)}
    (hv : natVal M2 p l = natVal M1 xp xl ^ natVal M1 yp yl % natVal M1 mp n) (hnm : NatNorm M2 p l)
    (hlc : l ≤ c) (hc64 : c < 2 ^ 40 ∧ p < 2 ^ 64) (hx : LiveExt R L1 L2)
    (hb : b1 - NCost costD costR costS costP xl yl n (stLen M1 st) (Nat.log2 (natVal M1 mp n)) ≤ b')
    (hnl : NatLive M2 R L2 p c)
    (hd : (c = 0 ∧ p = 0) ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L1))
    (hsb : StackBackL R L1 L2 st M1 M2)
    (hMF : MemFrame M1 M2 (R.rt ++ win { s with mem := M1 } (K + 0x498) 0x78 ++ [(zp, zp + 8 * zc)] ++
      ExpHyp.stWs M1 st))
    (hLF2 : LiveFrame M1 M2 L1 ([(zp, zp + 8 * zc)] ++ ExpHyp.stWs M1 st)) (hrs : ResSep M1 M2 st p c)
    (hF4 : MemFrame M2 m4 (R.rt ++ wN sp K ++ [(st + 8, st + 16)])) (hLF4 : LiveFrame M2 m4 L2 [(st + 8, st + 16)])
    (hinv4 : R.inv b' (dropAll L2 (stkRs M2 st)) g (view R.rt (dropAll L2 (stkRs M2 st)) m4))
    (s' : State) (hm' : s'.mem = m4) (hfs' : s'.fsBase = s.fsBase) (hdf' : s'.df = s.df)
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h3 : s'.regs 3 = BitVec.ofNat 64 l)
    (h1 : s'.regs 1 = BitVec.ofNat 64 c) :
    PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s' := by
  subst hm'
  obtain ⟨⟨hs4, hs14, -, -, -, -, -, hce, -⟩, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hmO, -, -, hmN, hyO, -, -, hyN, -, -,
    hxO, -, -, hxN, -, hxlc, -, -, ⟨-, hxz, -, hxcz⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hP
  obtain ⟨hal, hKs, hsp2, -, hg1, -, -, hwout, -⟩ := hce
  obtain ⟨hL1, hrs0, -, -, -, -, hl0, -, -, -, -, -, hdis0, hbb, -, -⟩ := id hN
  have hzO : 0 < zc → (InRanges zp (8 * zc) L ∨ Outside zp (8 * zc) R.rt) ∧ Apart zp (8 * zc) (sp - K) (K + 0x510) :=
    fun _ => by rw [← hxz, ← hxcz]; exact hxO (by omega)
  have esp : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have e14 : (s.regs 14).toNat = g := by rw [hs14, BitVec.toNat_ofNat]; omega
  have ex := (opnd_v0 (fun h => ⟨held_sub (hxO h).1 (Nat.le_refl _) (by omega),
    by have := (hxO h).2; unfold Apart at this ⊢; omega⟩) hLF hF hxN).1
  have ey := (opnd_v0 hyO hLF hF hyN).1
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
    have key : Apart p (8 * c) (sp - K) (K + 0x510) ∧ Apart p (8 * c) st 24 ∧
        (0 < stCap M1 st → Apart p (8 * c) (stW M1 st) (8 * stCap M1 st)) := by
      rcases hd with ⟨h, -⟩ | ⟨rfl, rfl⟩ | ⟨hin, hap⟩
      · omega
      · obtain ⟨hz1, hz2⟩ := hzO hc
        exact ⟨hz2, (hN.apart hz1).1, fun hc' => DivNil.apart_fresh hz1 (hN.arr hc').2 (hN.arr hc').1⟩
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
  have hFz : MemFrame s.mem s'.mem (R.rt ++ win s (K + 0x498) 0x78 ++ [(zp, zp + 8 * zc)]) := by
    refine ⟨fun a k ho => ?_, fun a k w => by rw [hF4.accessible, hMF.accessible, hF.accessible]⟩
    simp only [outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    have hw : Outside a k (wN sp K) := by
      simp only [win, esp, wN, outside_cons, outside_nil, and_true] at hwa ⊢; omega
    have hws := hN.outWs hrt
    have hhd : Outside a k [(st + 8, st + 16)] := by
      have := (hN.out hrt).1; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    have hwa' : Outside a k (win { s with mem := M1 } (K + 0x498) 0x78) := hwa
    rw [hF4.readLE a k (by simp only [outside_append]; exact ⟨⟨hrt, hw⟩, hhd⟩),
      hMF.readLE a k (by simp only [outside_append]; exact ⟨⟨⟨hrt, hwa'⟩, hz⟩, hws⟩),
      hF.readLE a k (by simp only [outside_append]; exact ⟨hrt, hw⟩)]
  have hLz : LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)] := ⟨fun a k hin hz => by
    obtain ⟨hws, hhd⟩ := hN.outL hin
    have hin1 : InRanges a k L1 := hin.of_subset fun _ hr => hN.mem hr
    rw [hLF4.readLE a k (hx.inRanges_old hin1) hhd,
      hLF2.readLE a k hin1 (by simp only [outside_append]; exact ⟨hz, hws⟩), hLF.readLE_nil a k hin]⟩
  refine ⟨hfs', hdf', p, l, c, h0, h3, h1, ?_, ?_, hlc, hc64, dropAll L2 (stkRs M2 st), b', hLE, by omega, ?_, ?_,
    ?_, hFz, hLz⟩
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp only [natVal, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero] at hv ⊢; exact hv
    · rw [← hv]; exact hrd p (8 * l) (Nat.le_refl _) (by omega) (by omega)
  · rcases hnm with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos l with hl | hl
      · exact Or.inl hl
      · right; rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h
  · rw [e14]; exact hinv4
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc
    exact ⟨a1, held_dropAll a2 (by omega) (hres hc).2.2.2, by rw [hF4.accessible]; exact a3, a4⟩
  · exact hd.imp_right (Or.imp_right fun ⟨hin, hap⟩ => ⟨hin, fun q hq => hap q (hN.mem hq)⟩)

end FvModexp.Amd64.ExpN
