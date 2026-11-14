import FvModexp.Proofs.Amd64.Exp.P2W2EnG
import FvModexp.Proofs.Amd64.Exp.P2W2Seg

set_option autoImplicit false

/-!
# P2W2 entry (amd64): the `growslice` call of the inline `stk.reserve(8w)` (agent divmc s66; ported from agent expmc's amd64 `W2En.enG2`)

`enG2`: entry of `growslice(w, len + nr, cap, len + nr - cap, Word)` → (fn+0x12b .. fn+0x15a: `R13 = CX` the new
capacity, `R11 = AX` the block, `0xb0 = R13`, `0x138 = R11`, `AX = R11 + 8·cap`, `BX = 8·(len + nr - cap)`) `enG3`.
Adapted from agent divmc's amd64 `(*stack).nat` `g2`/`gcall_pre` (Amd64/Nat/StackNatG2, StackNatCall).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

set_option maxRecDepth 20000 in
/-- the precondition of the `growslice` call from P2W2's frame (`RSP = sp - 0x8` at the callee) -/
theorem gpre {R : RtInv} {L : List (Nat × Nat)} {b g fs sp K w0 len0 cap0 nr : Nat} {S : State}
    (hce : CallW.CEnv R L g fs (sp - 0x8) K 0x238 S.mem) (hK : 4200 ≤ K) (hsv : RunIface.Serves R)
    (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 0x8)) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hra : S.mem.readLE (sp - 0x8) 8 < 2 ^ 47)
    (h0 : (S.regs 0).toNat = w0) (h3 : (S.regs 3).toNat = len0 + nr) (h1 : (S.regs 1).toNat = cap0)
    (h7 : (S.regs 7).toNat = len0 + nr - cap0) (h6 : (S.regs 6).toNat = wTy)
    (hk : cap0 < len0 + nr) (hln : len0 + nr ≤ 2 ^ 16)
    (hold : 0 < cap0 → w0 + 8 * cap0 ≤ 2 ^ 48 ∧ S.mem.accessible w0 (8 * cap0) false = true ∧
      Apart w0 (8 * cap0) (sp - 0x8 - K) (K + 0x238))
    (hcost : 8 * growCap8 (len0 + nr) cap0 ≤ b) (hinv : R.inv b L g (view R.rt L S.mem)) :
    GrowslicePre64 4096 S ∧ StackRoom64 S 4096 5 ∧
      LiveAt R grE (growsliceArgs64 S) L b (growsliceRound64 S) (S.regs 14).toNat S.mem (liveWin64 S 4096 5) := by
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce
  have tsp : (S.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have tg : (S.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have hwT : Apart wTy 16 (sp - 0x8 - K) (K + 0x238) := apart_of_data hd 1 (by decide) (by decide) hacc
  unfold Apart at hga hwT
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts hd
  rw [wTy_eq] at ht1 ht2 ht3
  refine ⟨⟨⟨⟨by rw [tsp]; exact hra, by rw [tsp]; omega, by rw [tsp]; omega, by rw [tsp]; omega, ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, fun hp => ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tsp]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [h6]; exact ⟨by decide, ht3⟩
  · simp only [typSize, h6]; exact ht1
  · simp only [typPtrBytes, h6]; exact ht2
  · omega
  · omega
  · omega
  · omega
  · rw [h6]; simp only [calleeStack64, tsp, outside_cons, outside_nil, and_true]; omega
  · have e : (S.regs 3).toNat - (S.regs 7).toNat = cap0 := by omega
    unfold GrowsliceOld64
    rw [e] at hp ⊢
    obtain ⟨a1, a2, a3⟩ := hold hp
    unfold Apart at a3
    rw [h0]
    exact ⟨a1, a2, by simp only [calleeStack64, tsp, outside_cons, outside_nil, and_true]; omega⟩
  · rw [tg]; omega
  · rw [tg]; exact hg2
  · rw [tg, tsp]; omega
  · rw [tg]; simp only [calleeStack64, tsp, outside_cons, outside_nil, and_true]; omega
  · rw [← grE_eq]; simp only [growsliceArgs64, h0, h3, h1, h7, h6]; exact hsv.2.2.2.1 _ _ _ _ _ (by omega)
  · rw [tg]; exact hinv
  · simp only [growsliceRound64, h3, h1]; exact hcost
  · intro r hr
    have := hLs r hr
    simp only [liveWin64, calleeStack64, tsp, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro r hr
    simp only [liveWin64, calleeStack64, tsp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hrt.of_sub (by simp only; omega) (by simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enG2 {impl : List Amd64.Segment} {R : RtInv}
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    {ret : W64} {Q : State → Prop}
    {b : Nat} {L : List (Nat × Nat)} {g fs sp K st lm w0 len0 cap0 : Nat} {M : Memory}
    (hce : CallW.CEnv R L g fs (sp - 0x8) K 0x238 M) (hK : 4200 ≤ K) (hsv : RunIface.Serves R)
    (hk : cap0 < len0 + 8 * W lm) (hn : W lm ≤ 128) (hl16 : len0 + 8 * W lm + 3 ≤ 2 ^ 16)
    (hc40 : cap0 < 2 ^ 40) (hw64 : w0 < 2 ^ 64)
    (hold : 0 < cap0 → w0 + 8 * cap0 ≤ 2 ^ 48 ∧ M.accessible w0 (8 * cap0) false = true ∧
      Apart w0 (8 * cap0) (sp - 0x8 - K) (K + 0x238))
    (hcost : 8 * growCap8 (len0 + 8 * W lm) cap0 ≤ b) (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 grE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (h5 : S.regs 5 = BitVec.ofNat 64 (sp + 0x1c8)) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 w0) (h3 : S.regs 3 = BitVec.ofNat 64 (len0 + 8 * W lm))
    (h1 : S.regs 1 = BitVec.ofNat 64 cap0) (h7 : S.regs 7 = BitVec.ofNat 64 (len0 + 8 * W lm - cap0))
    (h6 : S.regs 6 = BitVec.ofNat 64 wTy) (hmem : S.mem = M)
    (sret : M.readLE (sp - 0x8) 8 = grRet) (rd0 : M.readLE (sp + 0xb8) 8 = len0 + 8 * W lm - cap0)
    (rb8 : M.readLE (sp + 0xa8) 8 = len0) (r140 : M.readLE (sp + 0xf0) 8 = 8 * W lm)
    (r3d8 : M.readLE (sp + 0x208) 8 = st) (r148 : M.readLE (sp + 0xf8) 8 = W lm)
    (K' : ∀ (S' : State) (M' : Memory) (p gc : Nat),
      S'.rip = BitVec.ofNat 64 enJ → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = BitVec.ofNat 64 (sp + 0x1c8) →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 (W lm) → S'.regs 12 = BitVec.ofNat 64 len0 →
      S'.regs 13 = BitVec.ofNat 64 gc → S'.regs 15 = BitVec.ofNat 64 (8 * W lm) →
      S'.regs 11 = BitVec.ofNat 64 p → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase = S.fsBase → S'.xmm 15 = 0 → S'.df = S.df → S'.mem = M' →
      gc = growCap8 (len0 + 8 * W lm) cap0 → InRanges p (8 * gc) R.rt → ApartAll p (8 * gc) L →
      p % 8 = 0 → p + 8 * gc ≤ 2 ^ 48 → M'.accessible p (8 * gc) true = true →
      MemFrame M M' (R.rt ++ [(sp - 0x8 - 4096, sp + 0x28), (sp + 0xb0, sp + 0xb8), (sp + 0x138, sp + 0x140)]) →
      LiveFrame M M' L [] → M'.regions = M.regions →
      R.inv (b - 8 * gc) (L ++ [(p, p + 8 * gc)]) g (view R.rt (L ++ [(p, p + 8 * gc)]) M') →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hce' := hce
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce'
  have tsp : (S.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hpre := gpre (L := L) (b := b) (w0 := w0) (len0 := len0) (cap0 := cap0) (nr := 8 * W lm)
    (by rw [hmem]; exact hce) hK hsv hsp h14 (by rw [hmem, sret]; decide) (by rw [h0, BitVec.toNat_ofNat]; omega)
    (by rw [h3, BitVec.toNat_ofNat]; omega) (by rw [h1, BitVec.toNat_ofNat]; omega)
    (by rw [h7, BitVec.toNat_ofNat]; omega) (by rw [h6, BitVec.toNat_ofNat]; decide) hk (by omega)
    (by rw [hmem]; exact hold) hcost (by rw [hmem]; exact hinv)
  refine ReachesRet.call_regions (hgr _ _) hpc hpre fun S1 hpc1 hq hrg => ?_
  obtain ⟨ptr, junk, f1', x1, yh1, m1, zh1, kr1, hs1, hMF, hLF, ⟨hobj, hapL⟩, hapS, hinv1⟩ := hq
  subst hs1
  have t3 : (S.regs 3).toNat = len0 + 8 * W lm := by rw [h3, BitVec.toNat_ofNat]; omega
  have t1 : (S.regs 1).toNat = cap0 := by rw [h1, BitVec.toNat_ofNat]; omega
  have hround : growsliceRound64 S = 8 * growCap8 (len0 + 8 * W lm) cap0 := by
    simp only [growsliceRound64, t3, t1]
  simp only [growsliceObj64, Fresh, t3, t1] at hobj
  rw [hround] at hapL hinv1
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, -, -⟩ := hobj
  have hgcl := le_growCap8 (len0 + 8 * W lm) cap0
  have hgcb := growCap_lt len0 (8 * W lm) cap0 (by omega) (by omega)
  rw [show (8 * W lm + 3) / 4 * 4 = 8 * W lm by omega] at hgcb
  have hpw := hpin.apart hrt
  unfold Apart at hpw
  rw [hmem] at hMF hLF hrg
  simp only [calleeStack64, tsp] at hMF
  have hrd : ∀ a, sp + 0x28 ≤ a → a + 8 ≤ sp + 0x230 → m1.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩
  have q0 := (hrd _ (by omega) (by omega)).trans rd0
  have q1 := (hrd _ (by omega) (by omega)).trans rb8
  have q3 := (hrd _ (by omega) (by omega)).trans r140
  have q4 := (hrd _ (by omega) (by omega)).trans r3d8
  have q9 := (hrd _ (by omega) (by omega)).trans r148
  have sret' : M.readLE (sp - 0x8) 8 = 6201163 := sret
  have sret'' : S.mem.readLE (sp - 0x8) 8 = 6201163 := by rw [hmem]; exact sret
  have hsp8 : BitVec.ofNat 64 (sp - 0x8) + 8#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hp64 : ptr.toNat < 2 ^ 64 := ptr.isLt
  have esub : BitVec.ofNat 64 (len0 + 8 * W lm) - BitVec.ofNat 64 (len0 + 8 * W lm - cap0) =
      BitVec.ofNat 64 cap0 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine SegProg.lift P2W2Seg.codeIn (r := BitVec.ofNat 64 mcE) ?_
  janus64_run [q0, q1, q3, q4, sret', sret'', hsp, hsp8, h3, esub] until [mcE]
  generalize hgc : growCap8 (len0 + 8 * W lm) cap0 = gc at *
  generalize hM2 : ((m1.writeLE (sp + 0x138) 8 ptr.toNat).writeLE (sp + 0xb0) 8 gc).writeLE (sp - 0x8) 8 6201215 = M2
  have hws : MemFrame m1 M2 [(sp + 0xb0, sp + 0xb8), (sp + 0x138, sp + 0x140), (sp - 0x8, sp)] := by
    rw [← hM2]; janus_frame
  have hwr : LiveSep [(sp + 0xb0, sp + 0xb8), (sp + 0x138, sp + 0x140), (sp - 0x8, sp)] R.rt := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hrt.of_sub (by simp only; omega) (by simp only; omega)
  have hF2 : MemFrame M M2 (R.rt ++ [(sp - 0x8 - 4096, sp + 0x28), (sp + 0xb0, sp + 0xb8), (sp + 0x138, sp + 0x140)]) := by
    refine MemFrame.trans hMF hws fun a k ho => ⟨?_, ?_⟩
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨ho.1, by omega, by omega⟩
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨by omega, by omega, by omega⟩
  have hrg1 : m1.regions = M.regions := hrg
  have hrg2 : M2.regions = M.regions := by
    rw [← hrg1, ← hM2]; simp only [Janus.Arm64.Memory.regions_writeLE]
  have hce2 : CallW.CEnv R L g fs (sp - 0x8) K 0x238 M2 := by
    refine CallW.CEnv.frame hce hF2 hrg2 (fun r hr _ => ?_) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold Apart at hga f6
      rcases hr with rfl | rfl | rfl <;> simp only <;>
        exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    · unfold Apart at hga; simp only [outside_cons, outside_nil, and_true]; omega
    · unfold Apart at f6; simp only [outside_cons, outside_nil, and_true]; omega
  have hinv2 : R.inv (b - 8 * gc) (L ++ [(ptr.toNat, ptr.toNat + 8 * gc)]) g
      (view R.rt (L ++ [(ptr.toNat, ptr.toNat + 8 * gc)]) M2) := by
    have := RtInv.inv_frame hws hwr hinv1
    rwa [h14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  have hrd2 : ∀ a, (a + 8 ≤ sp + 0xb0 ∨ sp + 0xb8 ≤ a) → (a + 8 ≤ sp + 0x138 ∨ sp + 0x140 ≤ a) →
      (a + 8 ≤ sp - 0x8 ∨ sp ≤ a) → M2.readLE a 8 = m1.readLE a 8 := fun a h1 h2 h3 => by
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hpacc2 : M2.accessible ptr.toNat (8 * gc) true = true := by
    rw [← hM2]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hpacc
  have hal8' : ptr.toNat % 8 = 0 := hal8 (Or.inr (by omega))
  refine enG3 hmc (b := b) (L := L) (st := st) (lm := lm) (len0 := len0) (cap0 := cap0)
    (p := ptr.toNat) (gc := gc) (M := M2) hce2 hK hsv hk (by omega) (by omega) hn (by omega) hpin hp48 hpacc2 hinv2
    _ rfl ?hsp ?h14 ?h5 ?hx15 ?hdf ?h0 ?h3 rfl ?sret ?rc0 ?rb8 ?r198 ?r140 ?r3d8 ?r148 ?K
  case K =>
    intro S' M' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 hF3 hLF3 hrg3 hinv3
    refine K' S' M' ptr.toNat gc e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 ?_ e12 ?_ e14 rfl hpin hapL hal8' hp48
      ?_ ?_ ?_ (hrg3.trans hrg2) hinv3
    · exact e11
    · rw [e13]; first | rfl | exact hdf.symm
    · rw [hF3.accessible]; exact hpacc2
    · refine MemFrame.trans hF2 hF3 fun a k ho => ⟨ho, ?_⟩
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨ho.1, by omega, by omega⟩
    · refine ⟨fun a k hin _ => ?_⟩
      obtain ⟨r, hr, h1, h2⟩ := hin
      have hw := hLs r hr
      have hb := hapL r hr
      simp only [outside_cons, outside_nil, and_true] at hw
      unfold Apart at hb
      rw [hLF3.readLE a k ⟨r, List.mem_append_left _ hr, h1, h2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
        hws.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
        hLF.readLE a k ⟨r, hr, h1, h2⟩ trivial]
  case hsp =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  case h14 => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case h5 => simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case hx15 => simp only [↓reduceIte]; rfl
  case hdf => rfl
  case h0 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]; omega
  case h3 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  case sret => rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_self]
  case rc0 =>
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  case r198 =>
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]
  case rb8 => rw [hrd2 _ (by omega) (by omega) (by omega)]; exact q1
  case r140 => rw [hrd2 _ (by omega) (by omega) (by omega)]; exact q3
  case r3d8 => rw [hrd2 _ (by omega) (by omega) (by omega)]; exact q4
  case r148 => rw [hrd2 _ (by omega) (by omega) (by omega)]; exact q9

end FvModexp.Amd64.P2W2
