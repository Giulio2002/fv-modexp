import FvModexp.Proofs.Amd64.Exp.P2QG
import FvModexp.Proofs.Amd64.Exp.P2W4EnCtx
import FvModexp.Proofs.Amd64.Exp.P2W4EnA
import FvModexp.Proofs.Amd64.Exp.P2W4EnG2
import FvModexp.Proofs.Amd64.Exp.P2W4EnJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): from the entry to `rsE` (after the inline `stk.reserve(8w)`) (agent top s48, port of divmc s66;
amd64 twin of `Arm64.P2W2.ent`, amd64 idioms of agent expmc's `W2En.enStep`)

`ent` = `enA` + (`enG2`) + `enJn`; the continuation `KR` gets the memory at `rsE` with its frames from the entry
memory, the stack's array kept or fresh (`ArrKF`), `len = len₀ + 8w`, the frame slots `ESl` and the effective budget
`b1 ≥ b` (invariant at `b1 + stkR (HW len₀ lm)`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the facts at `rsE` (continuation of `ent`) -/
@[reducible] def RsK (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State) (ret0 : W64) (Q : State → Prop) : Prop :=
  ∀ (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [(sp - 0x8 - K, sp + 0x358), (st, st + 24)]) →
    MemFrame s.mem M (R.rt ++ [(sp - 0x8 - K, sp + 0x2f8), (sp + 0x318, sp + 0x358), (st, st + 24)]) →
    LiveFrame s.mem M L [(st, st + 24)] → M.regions = s.mem.regions → LiveExt R L L1 →
    ArrKF R L st s.mem M → stLen M st = stLen s.mem st + 20 * W lm → stLen M st ≤ stCap M st →
    stCap M st < 2 ^ 40 → NatLive M R L1 (stW M st) (stCap M st) →
    (¬(stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) → (stW M st, stW M st + 8 * stCap M st) ∈ L1) →
    ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) →
    b ≤ b1 → R.inv (b1 + stkR (HW (stLen s.mem st) lm) M st) L1 g (view R.rt L1 M) →
    ∀ S : State, S.rip = BitVec.ofNat 64 rsE → S.regs 4 = BitVec.ofNat 64 sp → S.regs 7 = BitVec.ofNat 64 st →
      S.regs 2 = BitVec.ofNat 64 (W lm) → S.regs 14 = BitVec.ofNat 64 g → S.fsBase = s.fsBase →
      S.xmm 15 = 0 → S.df = s.df → S.mem = M →
      ReachesRet (LibW.program.link impl) ret0 S Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the entry to `rsE`** -/
theorem ent {impl : List Amd64.Segment} {R : RtInv}
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {ret0 : W64} {Q : State → Prop}
    {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {zl : Nat} (hzl : zl < 2 ^ 64)
    (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 st) (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl)
    (h9 : s.regs 9 = BitVec.ofNat 64 xc) (h10 : s.regs 10 = BitVec.ofNat 64 lm)
    (KR : RsK impl R b L K g sp st bp r zp zc xp xl xc yp yl lm s ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 s Q := by
  have hP' := hP
  obtain ⟨he, hgl, hro, hwt, hlm2, hlm, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc,
    hzp, hzc, hz, hgO, hsok, hstw, hstg, hstfs, harr, hwbf, hwbA, hstf, hstnz, hl16, hbp, hr1d0, hr47, r1d8, r1e0,
    hone, hinv⟩ := hP'
  obtain ⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, hce, hsv⟩ := he
  have hce' := hce
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, -, f1, f2, f3, f4, f5, f6⟩ := hce'
  have hsok' := hsok
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok'
  unfold Apart at hstw hstg hstfs hga f6
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hok : R.ok wbE [2] := by rw [← wbE_eq]; exact hsv.2.2.2.2.2.1 _
  have hwacc0 : s.mem.accessible (sp - 0x8 - 4096) (4096 + 8) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hwrt : Outside (sp - 0x8 - 4096) (4096 + 8) R.rt := hrt.of_sub (by omega) (by omega)
  have hwL : LiveSep L [(sp - 0x8 - 4096, sp)] := LiveSep.sub_win hLs (by omega) (by omega)
  have h5 : s.regs 5 = BitVec.ofNat 64 bp := by rw [← hbp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hgs : g < 2 ^ 64 := by omega
  refine enA (M := s.mem) (w0 := stW s.mem st) (len0 := stLen s.mem st) (cap0 := stCap s.mem st) hal (by omega)
    (by omega) (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega)
    (Janus.Arm64.Memory.accessible_weaken _ k3) k4 (by omega) rfl rfl rfl (by omega) k7 k6 hlm hzp hzl (by omega)
    hxp (by omega) hxc (by rw [← hbp]; exact BitVec.isLt _) hr1d0 r1d8 r1e0 s
    hpc hs4 rfl h0 h3 h1 h7 h6 h8 h9 h10 h5 hs14 hx15 ?KJ ?KG
  case KJ =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 cm hF1 hrg1 hsl1
    have hF1' : MemFrame s.mem M1 [(sp - 0x8 - K, sp + 0x358)] := hF1.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hinvM1 : R.inv (b + stkR (HW (stLen s.mem st) lm) s.mem st) L g (view R.rt L M1) :=
      RtInv.inv_frame hF1' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        rw [show sp + 0x358 - (sp - 0x8 - K) = K + 0x360 by omega]; exact hrt) hinv
    refine enJn hwb (b1 := b + stkR (HW (stLen s.mem st) lm) s.mem st) (L1 := L) (w1 := stW s.mem st)
      (len0 := stLen s.mem st) (c1 := stCap s.mem st) (lm := lm)
      (M := M1) (by omega) (by omega) hal (by rw [hF1.accessible]; exact hwacc0) hwrt hwL
      (by rw [hF1.accessible]; exact k3) k4 k2 (by omega) (by rw [hF1.accessible]; exact hwbf) hwbA hok hinvM1 hgs hk k7
      (Janus.Arm64.Memory.readLE_lt _ _ _) (by omega) hW S1 c1 c2 c4 c9 c7 c8 c6 c10 cm ?_
    intro S3 M3 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 dm hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - 0x8 - K, sp + 0x358), (st, st + 24)]) := by
      refine MemFrame.trans hF1 hF3 fun a k ho => ⟨?_, ?_⟩ <;>
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      · omega
      · exact ⟨ho.1, by omega, by omega⟩
    have hFp : MemFrame s.mem M3 (R.rt ++ [(sp - 0x8 - K, sp + 0x2f8), (sp + 0x318, sp + 0x358), (st, st + 24)]) := by
      refine MemFrame.trans hF1 hF3 fun a k ho => ⟨?_, ?_⟩ <;>
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      · omega
      · exact ⟨ho.1, by omega, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] :=
      (LiveFrame.of_win hF1' (LiveSep.sub_win hLs (by omega) (by omega))).trans hLF3 fun _ _ h => h
    have hsl3 : ESl M3 sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) := by
      refine ESl.keep hsl1 (fun a k ha => hF3.readLE a k ?_)
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hk ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact k7
    have hnl3 : NatLive M3 R L (stW M3 st) (stCap M3 st) := by
      intro hc
      simp only [stW, stCap] at q1 q3 hc ⊢
      rw [q3] at hc; rw [q1, q3]
      obtain ⟨a1, a2, a3, a4⟩ := k5 hc
      exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
    exact KR M3 L b hF hFp hLF (hrg3.trans hrg1) (LiveExt.refl R L) (Or.inl ⟨q1, q3⟩) q2 hcap3 hc3 hnl3
      (fun h => absurd ⟨q1, q3⟩ h) hsl3 (Nat.le_refl _)
      (by rw [stkR_congr (show stCap M3 st = stCap s.mem st from q3)]; exact hinv3)
      S3 d1 d2 d3 (d4.trans c5) d9 (d10.trans c11) (d11.trans c12) (d12.trans c13) dm
  case KG =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 cm hF1 hrg1 hsl1 sret s0f8 s0f0 s0a8 s0b8
    have hF1' : MemFrame s.mem M1 [(sp - 0x8 - K, sp + 0x358)] := hF1.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hinvM1 : R.inv (b + stkR (HW (stLen s.mem st) lm) s.mem st) L g (view R.rt L M1) :=
      RtInv.inv_frame hF1' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        rw [show sp + 0x358 - (sp - 0x8 - K) = K + 0x360 by omega]; exact hrt) hinv
    have hce1 : CallW.CEnv R L g fs (sp - 0x8) K 0x360 M1 :=
      CallW.CEnv.frame hce (hF1'.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) hrg1
        (fun r hr _ => by
          simp only [List.mem_singleton] at hr; subst hr; simp only
          rw [show sp + 0x358 - (sp - 0x8 - K) = K + 0x360 by omega]; exact hacc)
        (by simp only [outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hsl1' := hsl1
    obtain ⟨-, -, -, -, -, -, -, -, a9, -⟩ := hsl1'
    have hk' : stCap s.mem st < stLen s.mem st + (20 * W lm + 3) / 4 * 4 := by omega
    have e8 : (20 * W lm + 3) / 4 * 4 = 20 * W lm := by omega
    have hgcb := growCap_lt _ _ _ hk' (by omega)
    rw [e8] at hgcb
    have hgcl := le_growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st)
    have hGE := P2Q.grow_eff (R := R) (b := b) (H := (HW (stLen s.mem st) lm)) (st := st) (M' := s.mem) (L := L)
      (g := g) (v := s.mem) hk' (by simp only [HW, StackNat.rnd]; omega) rfl
    rw [e8] at hGE
    refine enG2 hgr hmc (b := b + stkR (HW (stLen s.mem st) lm) s.mem st) (L := L) (fs := fs) (K := K) (st := st)
      (lm := lm) (w0 := stW s.mem st) (len0 := stLen s.mem st) (cap0 := stCap s.mem st) (M := M1) hce1 (by omega) hsv
      hk hW (by omega) k7 (Janus.Arm64.Memory.readLE_lt _ _ _) (fun hc => ?_) hGE.1 hinvM1 S1 c1 c2 c9 c3
      c11 (c12.trans hdf) c4 c5 c6 c7 c8 cm sret s0b8 s0a8 s0f0 a9 s0f8 ?_
    · obtain ⟨-, -, a3, a4⟩ := k5 hc
      obtain ⟨b1, -, -⟩ := harr hc
      exact ⟨a4, by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ a3,
        b1⟩
    intro S2 M2 p gc d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 dm hgc hpin hapL hp8 hp48 hpacc hF2 hLF2 hrg2 hinv2
    subst hgc
    have hx : LiveExt R L (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) :=
      ⟨[(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))], rfl, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]; exact ⟨hpin, hapL⟩,
        List.pairwise_singleton _ _⟩
    have hF12 : MemFrame s.mem M2 (R.rt ++ [(sp - 0x8 - K, sp + 0x358)]) := by
      refine MemFrame.trans hF1' hF2 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨by omega, ho.1, by omega⟩
    have hF12p : MemFrame s.mem M2 (R.rt ++ [(sp - 0x8 - K, sp + 0x2f8), (sp + 0x318, sp + 0x358)]) := by
      refine MemFrame.trans hF1 hF2 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨by omega, by omega⟩, ho.1, by omega⟩
    refine enJn hwb (b1 := b + stkR (HW (stLen s.mem st) lm) s.mem st -
        8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))
      (L1 := L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) (w1 := p)
      (len0 := stLen s.mem st) (c1 := growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st)) (lm := lm) (M := M2)
      (by omega) (by omega) hal (by rw [hF12.accessible]; exact hwacc0) hwrt
      (hx.liveSep hwL fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        exact hrt.of_sub (by omega) (by omega))
      (by rw [hF12.accessible]; exact k3) k4 (hx.held k2) (by omega) (by rw [hF12.accessible]; exact hwbf) hwbA hok
      hinv2 hgs hgcl hgcb (by omega) (by omega) hW S2 d1 d2 d4 d9 d7 d8 d6 d10 dm ?_
    intro S3 M3 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 gm hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - 0x8 - K, sp + 0x358), (st, st + 24)]) := by
      refine MemFrame.trans hF12 hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, ho.2.1⟩, ho.1, ho.2.2, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] := by
      refine ((LiveFrame.of_win hF1' (LiveSep.sub_win hLs (by omega) (by omega))).trans
        ⟨fun a k hin _ => hLF2.readLE a k hin trivial⟩ fun _ _ h => h).trans hLF3 fun a k h => hx.inRanges_old h
    have hsl3 : ESl M3 sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) := by
      refine ESl.keep (ESl.keep hsl1 (fun a k ha => hF2.readLE a k ?_)) (fun a k ha => hF3.readLE a k ?_)
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hgcl ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact hgcb
    have hkfG : ArrKF R L st s.mem M3 := Or.inr (by simp only [stW, stCap] at q1 q3 ⊢; rw [q1, q3]; exact ⟨hpin, hapL⟩)
    have hFp : MemFrame s.mem M3 (R.rt ++ [(sp - 0x8 - K, sp + 0x2f8), (sp + 0x318, sp + 0x358), (st, st + 24)]) := by
      refine MemFrame.trans hF12p hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, by omega, by omega⟩, ho.1, ho.2.2.2, by omega⟩
    obtain ⟨b1, hinv1, hb1⟩ := (P2Q.grow_eff (R := R) (b := b) (H := (HW (stLen s.mem st) lm)) (st := st) (M' := M3)
      (gc := growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))
      (L := L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) (g := g)
      (v := view R.rt (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) M3) hk'
      (by simp only [HW, StackNat.rnd]; omega) (by rw [e8])).2 hinv3 q3
    refine KR M3 _ b1 hF hFp hLF (hrg3.trans (hrg2.trans hrg1)) hx hkfG q2 hcap3 hc3 ?_ (fun _ => ?_) hsl3
      hb1 hinv1 S3 g1 g2 g3 (g4.trans d5) g9 ((g10.trans d11).trans c10) (g11.trans d12)
      ((g12.trans d13).trans c12) gm
    · intro hc
      simp only [stW, stCap] at q1 q3 hc ⊢
      rw [q1, q3]
      exact ⟨hp8, Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
        by simp only; omega⟩, by rw [hF3.accessible]; exact hpacc, hp48⟩
    · simp only [stW, stCap] at q1 q3 ⊢
      rw [q1, q3]; exact List.mem_append_right _ (List.mem_singleton_self _)

end FvModexp.Amd64.P2W4
