import FvModexp.Proofs.Arm64.Exp.W4EnPre
import FvModexp.Proofs.Arm64.Exp.W4CtxB

/-!
# window-4 entry (arm64): from the entry facts `EPre` and the frames of the entry segment to `W4Pro.CtxB` at `xnE`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

open FvModexp.Arm64.W4Pro (Obj AW stUp)

/-- the array after the reserve: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

/-- an entry object is an `Obj` of the context at `xnE` (live set `L1 ⊇ L`, level `l0 ≥ len`) -/
theorem obj_of_OE {R : RtInv} {L L1 : List (Nat × Nat)} {sp K st l0 a k : Nat} {M0 M : Memory}
    (h : OE R L sp K st M0 a k) (hx : LiveExt R L L1) (hkf : ArrKF R L st M0 M)
    (hl : stLen M0 st ≤ l0) (hl' : l0 ≤ stCap M st) :
    Obj R L1 sp K st l0 [] M a k := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hx.held h1, h2, h3, ?_, fun e he => by simp at he⟩
  rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · simp only [stUp, free, Apart] at h4 ⊢; rw [e1, e2]; rw [e2] at hl'; omega
  · have := W4Pro.apart_fresh hin hap h1
    simp only [stUp]; unfold Apart at this ⊢; omega

/-- an entry object keeps its bytes -/
theorem rd_of_OE {R : RtInv} {L : List (Nat × Nat)} {sp K st a k : Nat} {M0 M : Memory}
    (h : OE R L sp K st M0 a k) (hF : MemFrame M0 M (R.rt ++ [(sp - K, sp + 1040), (st, st + 24)]))
    (hLF : LiveFrame M0 M L [(st, st + 24)]) {a' k' : Nat} (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) :
    M.readLE a' k' = M0.readLE a' k' := by
  obtain ⟨hh, hw, hs, -⟩ := h
  unfold Apart at hw hs
  rcases hh with hL | hO
  · exact hLF.readLE a' k' (hL.sub h1 h2) (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine hF.readLE a' k' ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hO.of_sub h1 h2, by omega, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `CtxB` at `xnE` from the entry facts and the frames of the entry segment (entry memory `s.mem`, `xnE` memory `M`) -/
theorem ctxB_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp ylen mp n mc : Nat}
    {s : State} {r29 : BitVec 64} {ret : Nat}
    (hP : EPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s)
    {M : Memory} {L1 : List (Nat × Nat)} (hF : MemFrame s.mem M (R.rt ++ [(sp - K, sp + 1040), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hkf : ArrKF R L st s.mem M) (hlen : stLen M st = stLen s.mem st + StackNat.rnd (23 * n))
    (hcap : stLen M st ≤ stCap M st) (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hsl : ESl M sp st r29 ret zp zc xp xl xc yp ylen mp n mc (stLen s.mem st)) :
    W4Pro.CtxB R L1 g sp K n mp mc (s.mem.readLE mp (8 * n)) yp ylen (s.mem.readLE yp (8 * ylen))
      (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen M st) ret r29 [] M := by
  obtain ⟨he, hK20, hgl, hro, hty, hn, hn128, hmc, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl',
    hxO, hxa, hx48, hxN, hxl, hxl', hxp, hxc, hzp, hzc, hz, hgO, hsok, hstw, hstg, harr, hwbf, hwbA, hstf, hl16,
    hinv⟩ := hP
  have he' := he
  obtain ⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩ := he'
  simp only [outside_cons] at hgo
  obtain ⟨hgw, hgrt⟩ := hgo
  have hout : Outside (sp - K) (K + 1040) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1040 - (sp - K) = K + 1040 by omega] at this
  unfold Apart at hstw hstg
  have hl0 : stLen s.mem st ≤ stLen M st := by omega
  have obj := fun {a k : Nat} (h : OE R L sp K st s.mem a k) => obj_of_OE h hx hkf hl0 hcap
  have rd := fun {a k a' k' : Nat} (h : OE R L sp K st s.mem a k) (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) =>
    rd_of_OE (a' := a') (k' := k') h hF hLF h1 h2
  have hgr : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := by
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hgrt, by omega, by omega⟩
  have hacc' : ∀ a k w, M.accessible a k w = s.mem.accessible a k w := fun a k w => hF.accessible a k w
  have hLs1 : LiveSep L1 [(sp - K, sp + 1040)] := hx.liveSep hLs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only
    rw [show sp + 1040 - (sp - K) = K + 1040 by omega]; exact hout
  have hce0 : CallW.CEnv R L g sp K 1040 s.mem :=
    ⟨hal, hK', hsp2, hacc, hg1, hg2, hg3, hout, by unfold Apart; omega, hgrt, hLs, hd, hro⟩
  have hce : CallW.CEnv R L1 g sp K 1040 M := by
    have := CallW.CEnv.frame hce0 hF hrg (fun r hr _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; rw [show sp + 1040 - (sp - K) = K + 1040 by omega]; exact hacc
      · simp only; rw [show st + 24 - st = 24 by omega]; exact hsok.2.2.1)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, a12, a13⟩ := this
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hLs1, a12, a13⟩
  have hrn : 0 < StackNat.rnd (23 * n) := by simp only [StackNat.rnd]; omega
  have hcap0 : 0 < stCap M st := by omega
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17⟩ := hsl
  have hsok' := hsok
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok'
  have hsthL : InRanges st 24 L1 ∨ Outside st 24 R.rt := hx.held k2
  have inp := fun {a k : Nat} (h : OE R L sp K st s.mem a k) (ha : s.mem.accessible a k false = true)
      (h48 : a + k ≤ 2 ^ 48) => (⟨by rw [hacc']; exact ha, h48, hx.held h.1,
        by have := h.2.1; unfold Apart at this ⊢; omega⟩ :
        M.accessible a k false = true ∧ a + k ≤ 2 ^ 48 ∧ (InRanges a k L1 ∨ Outside a k R.rt) ∧
          Apart a k (sp - 4288) (4288 + 1040))
  -- the array after the reserve
  have harr' : 0 < stCap M st → AW sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8 := by
    intro hc
    rcases hkf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e1, e2]; rw [e2] at hc; exact harr hc
    · have h1 := W4Pro.out_inR hout hin
      have h2 := W4Pro.out_inR hgrt hin
      simp only [AW, Apart]; unfold Apart at h1 h2; omega
  have hup := harr' hcap0
  simp only [AW, Apart] at hup
  refine ⟨?env, hce, hK, hK20, hn, hn128, hmc, hmc', inp hmO hma hm48, obj hmO, rd hmO (Nat.le_refl _) (Nat.le_refl _),
    ?mN, inp hyO hya hy48, obj hyO, rd hyO (Nat.le_refl _) (Nat.le_refl _), ?yi, ?yi0, hyl, hyl', hzc, ?z, ?fin,
    hsthL, by simp only [AW]; unfold Apart; omega, ⟨k1, hsthL, by rw [hacc']; exact k3, k4, hnl, hcap, hc40⟩,
    by omega, Nat.le_refl _, hcap0, harr', ?ug, ?uw, ?su, ?glob, obj hgO, hwbA, hro, hty, q15, q16, q17, q8, q7, q14,
    q13, q9⟩
  case env =>
    refine ⟨hal, by omega, hsp2, by rw [hacc']; exact Memory.accessible_mono _ hacc (by omega) (by omega), hg1,
      by rw [hacc']; exact hg2, by rw [hgr]; omega, hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgrt, ?_⟩
    exact LiveSep.sub_win hLs1 (by omega) (by omega)
  case mN =>
    rcases hmN with h | h
    · exact Or.inl h
    · right; rw [rd hmO (by omega) (by omega)]; exact h
  case yi => rw [rd hyO (by omega) (by omega)]
  case yi0 =>
    rcases hyN with h | h
    · omega
    · exact Nat.pos_of_ne_zero h
  case z =>
    intro h2
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hz h2
    refine ⟨⟨h2, hzc, by rw [hacc']; exact b2, b3, hx.held b1.1, by have := b1.2.1; unfold Apart at this ⊢; omega,
      by unfold Apart at b5 ⊢; omega⟩, b4, obj b1, b6, b7⟩
  case fin =>
    have e840 : segAddr LibExp.program DeferW.fnW4 = 1801824 := by decide
    refine ⟨hal, by omega, hsp2, by rw [hacc']; exact Memory.accessible_mono _ hacc (by omega) (by omega), hg1,
      by rw [hacc']; exact hg2, by rw [hgr]; omega, by unfold Apart; omega, q3, by rw [e840]; exact q4, q5, q6, k4,
      by rw [hacc']; exact k3, by simp only [stLen, stCap] at hcap hlen ⊢; omega, by unfold Apart; omega,
      by unfold Apart; omega, q1, q2⟩
  case ug => simp only [stUp, Apart]; omega
  case uw => simp only [stUp, AW, Apart]; omega
  case su =>
    rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [free, Apart] at hstf; simp only [stUp, Apart]; rw [e1, e2]; rw [e2] at hcap; omega
    · have := W4Pro.apart_fresh hin hap k2
      simp only [stUp]; unfold Apart at this ⊢; omega
  case glob =>
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hgl
    have hrdG : ∀ j, j + 8 ≤ 32 → M.readLE (RunIface.gA + j) 8 = s.mem.readLE (RunIface.gA + j) 8 :=
      fun j hj => rd hgO (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hacc']; exact g8, g9, g10, by rw [hacc']; exact g11, g12, g13⟩
    · rw [g5, hrdG 8 (by omega), ← g5]; exact g1
    · rw [g6, hrdG 16 (by omega), ← g6]; exact g2
    · rw [g7, hrdG 24 (by omega), ← g7]; exact g3
    · have := hrdG 0 (by omega); simp only [Nat.add_zero] at this
      show M.readLE RunIface.gA 8 = 40; rw [this]; exact g4

end FvModexp.Arm64.W4En
