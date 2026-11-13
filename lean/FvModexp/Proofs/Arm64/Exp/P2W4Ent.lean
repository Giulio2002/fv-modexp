import FvModexp.Proofs.Arm64.Exp.P2Q
import FvModexp.Proofs.Arm64.Exp.P2W4Pre
import FvModexp.Proofs.Arm64.Exp.P2W4EnA
import FvModexp.Proofs.Arm64.Exp.P2W4EnG
import FvModexp.Proofs.Arm64.Exp.P2W4EnJ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): from the entry to `rsE` (after the inline `stk.reserve(20w)`) (agent infra)

`ent` = `enA` + (`enG2`) + `enJn` composed (window-4 copy of `P2W2.ent`, as agent expmc's window-2 `W2En.enStep`); the continuation `KR` gets the
memory at `rsE` with its frames from the entry memory, the stack's array kept or fresh (`ArrKF`), `len = len₀ + 20w`,
the frame slots `ESl` and the budget `b - stackNatCost len₀ (8w)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

/-- the facts at `rsE` (continuation of `ent`) -/
@[reducible] def RsK (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl
    lm ret : Nat) (s : State) (ret0 : BitVec 64) (Q : State → Prop) : Prop :=
  ∀ (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [(sp - K, sp + 848), (st, st + 24)]) →
    MemFrame s.mem M (R.rt ++ [(sp - K, sp + 744), (sp + 760, sp + 848), (st, st + 24)]) →
    LiveFrame s.mem M L [(st, st + 24)] → M.regions = s.mem.regions → LiveExt R L L1 →
    ArrKF R L st s.mem M → stLen M st = stLen s.mem st + 20 * W lm → stLen M st ≤ stCap M st →
    stCap M st < 2 ^ 40 → NatLive M R L1 (stW M st) (stCap M st) →
    (¬(stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) → (stW M st, stW M st + 8 * stCap M st) ∈ L1) →
    ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st) →
    b ≤ b1 → R.inv (b1 + stkR (HW (stLen s.mem st) lm) M st) L1 g (view R.rt L1 M) →
    ∀ S : State, S.pc = BitVec.ofNat 64 rsE → S.sp = BitVec.ofNat 64 sp → S.regs 3 = BitVec.ofNat 64 st →
      S.regs 9 = BitVec.ofNat 64 (W lm) → S.regs 18 = s.regs 18 → S.regs 28 = BitVec.ofNat 64 g →
      S.regs 29 = BitVec.ofNat 64 (sp - 8) → S.mem = M →
      ReachesRet (LibW.program.link impl) ret0 S Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the entry to `rsE`** -/
theorem ent (impl : List Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibW.program.link impl) mcE 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hr48 : ret < 2 ^ 48)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 yl)
    (h10 : s.regs 10 = BitVec.ofNat 64 lm) (h30 : s.regs 30 = BitVec.ofNat 64 ret)
    (KR : RsK impl R b L K g sp st zp zc xp xl xc yp yl lm ret s ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 s Q := by
  have hP' := hP
  obtain ⟨he, hK20, hgl, hro, hty, hlm2, hlm, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc,
    hzp, hzc, hz, hgO, hsok, hstw, hstg, harr, hwbf, hwbA, hstf, hstnz, hl16, hone, hinv⟩ := hP'
  have he' := he
  obtain ⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩ := he'
  have hsok' := hsok
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok'
  have hout : Outside (sp - K) (K + 848) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 848 - (sp - K) = K + 848 by omega] at this
  unfold Apart at hstw hstg
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have e1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by apply BitVec.eq_of_toNat_eq; simp
  have e9 : s.regs 9 = BitVec.ofNat 64 (s.regs 9).toNat := by apply BitVec.eq_of_toNat_eq; simp
  have hok : R.ok wbE [2] := by rw [← wbE_eq]; exact hsv.2.2.2.2.2.1 _
  refine enA impl ret0 Q sp g st zp (s.regs 1).toNat zc xp xl xc yp yl (s.regs 9).toNat lm ret
    (stW s.mem st) (stLen s.mem st) (stCap s.mem st) (s.regs 29) s.mem hal (by omega) hsp2
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) (Memory.accessible_weaken _ k3) k4
    (by omega) rfl rfl rfl (by omega) k7 hlm hr48 hzp (BitVec.isLt _) (by omega) hxp (by omega) hxc (by omega)
    (by omega) (BitVec.isLt _) s hpc hs1 h0 e1 h2 h3 h4 h5 h6 h7 h8 e9 h10 hs28 rfl h30 rfl ?KJ ?KG
  case KJ =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hF1p hrg1 hsl1
    have hF1 : MemFrame s.mem M1 [(sp - 8, sp + 848)] := hF1p.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hinvM1 : R.inv (b + stkR (HW (stLen s.mem st) lm) s.mem st) L g (view R.rt L M1) := RtInv.inv_frame hF1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hout.of_sub (by omega) (by omega)) hinv
    refine enJn impl R hwb ret0 Q (b + stkR (HW (stLen s.mem st) lm) s.mem st) L g sp st (stW s.mem st) (stLen s.mem st) (stCap s.mem st) (W lm) M1 hal
      (by omega) hsp2 (by rw [hF1.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega))
      (LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega)) (LiveSep.sub_win hLs (by omega) (by omega))
      (by rw [hF1.accessible]; exact k3) k4 k2 (by omega) (by rw [hF1.accessible]; exact hwbf) hwbA hok hinvM1
      (by omega) hk k7 (Memory.readLE_lt _ _ _) (by omega) hW S1 c1 c2 c3 c5 c6 c7 c8 c10 c12 ?_
    intro S3 M3 d1 d2 d3 d4 d5 d6 d7 d8 hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 848), (st, st + 24)]) := by
      refine MemFrame.trans hF1 hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨by omega, ho.1, ho.2.2, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] :=
      (LiveFrame.of_win hF1 (LiveSep.sub_win hLs (by omega) (by omega))).trans hLF3 fun _ _ h => h
    have hFp : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 744), (sp + 760, sp + 848), (st, st + 24)]) := by
      refine MemFrame.trans hF1p hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨by omega, by omega⟩, ho.1, ho.2.2.2, by omega⟩
    have hsl3 : ESl M3 sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st) := by
      refine ESl.keep hsl1 (fun a k ha => hF3.readLE a k ?_) (by omega)
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hk ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact k7
    refine KR M3 L b hF hFp hLF (hrg3.trans hrg1) (LiveExt.refl R L) (Or.inl ⟨q1, q3⟩) q2 hcap3 hc3 ?_ (fun h => absurd ⟨q1, q3⟩ h) hsl3
      (Nat.le_refl _) (by rw [stkR_congr (show stCap M3 st = stCap s.mem st from q3)]; exact hinv3) S3 d1 d2 d3 (d4.trans c4) (d5.trans c9) d6 (d7.trans c11) d8
    intro hc
    simp only [stW, stCap] at q1 q3 hc ⊢
    rw [q3] at hc; rw [q1, q3]
    obtain ⟨a1, a2, a3, a4⟩ := k5 hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  case KG =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hF1p hrg1 hsl1 q240 q176 q192 q232 q248
    have hF1 : MemFrame s.mem M1 [(sp - 8, sp + 848)] := hF1p.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hsl1' := hsl1
    obtain ⟨-, -, -, -, -, -, -, -, a9, -⟩ := hsl1'
    have hk' : stCap s.mem st < stLen s.mem st + (20 * W lm + 3) / 4 * 4 := by omega
    have e8 : (20 * W lm + 3) / 4 * 4 = 20 * W lm := by omega
    have hcostG := growRound_le_cost _ _ _ hk'
    have hgcb := growCap_lt _ _ _ hk' (by omega)
    rw [e8] at hcostG hgcb
    have hgcl := le_growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st)
    have hGE := P2Q.grow_eff (R := R) (b := b) (H := (HW (stLen s.mem st) lm)) (st := st) (M' := s.mem) (L := L) (g := g) (v := s.mem) hk'
      (by simp only [HW, StackNat.rnd]; omega) rfl
    rw [e8] at hGE
    refine enG2 impl R hgr hmc ret0 Q (b + stkR (HW (stLen s.mem st) lm) s.mem st) L g sp K st (W lm) (stW s.mem st) (stLen s.mem st)
      (stCap s.mem st) s he hk hW (by omega) (Memory.readLE_lt _ _ _) (fun hc => ?_) hGE.1 hinv S1 M1 c1 c2 c3
      c4 c5 c6 c7 c8 c10 c12 hF1 q240 q176 q192 q232 a9 q248 ?_
    · obtain ⟨-, -, a3, a4⟩ := k5 hc
      exact ⟨a4, Memory.accessible_weaken _ a3, (harr hc).1⟩
    intro S2 M2 p gc d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 hgc hpin hapL hp8 hp48 hpacc hF2 hLF2 hrg2 hinv2
    subst hgc
    have hx : LiveExt R L (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) :=
      ⟨[(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))], rfl, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]; exact ⟨hpin, hapL⟩,
        List.pairwise_singleton _ _⟩
    have hF12 : MemFrame s.mem M2 (R.rt ++ [(sp - K, sp + 848)]) := by
      refine MemFrame.trans hF1 hF2 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨by omega, ho.1, by omega⟩
    have hF12p : MemFrame s.mem M2 (R.rt ++ [(sp - K, sp + 744), (sp + 760, sp + 848)]) := by
      refine MemFrame.trans hF1p hF2 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨by omega, by omega⟩, ho.1, by omega⟩
    refine enJn impl R hwb ret0 Q (b + stkR (HW (stLen s.mem st) lm) s.mem st - 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))
      (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) g sp st p
      (stLen s.mem st) (growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st)) (W lm) M2 hal (by omega)
      hsp2 (by rw [hF12.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega))
      (LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega))
      (hx.liveSep (LiveSep.sub_win hLs (by omega) (by omega)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        exact hout.of_sub (by omega) (by omega))
      (by rw [hF12.accessible]; exact k3) k4 (hx.held k2) (by omega) (by rw [hF12.accessible]; exact hwbf) hwbA hok
      hinv2 (by omega) hgcl hgcb (by omega) (by omega) hW S2 d1 d2 d3 d5 d6 d7 d8 d10 d12 ?_
    intro S3 M3 e1 e2 e3 e4 e5 e6 e7 e8 hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 848), (st, st + 24)]) := by
      refine MemFrame.trans hF12 hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, ho.2.1⟩, ho.1, ho.2.2, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] := by
      refine ((LiveFrame.of_win hF1 (LiveSep.sub_win hLs (by omega) (by omega))).trans
        ⟨fun a k hin _ => hLF2.readLE a k hin trivial⟩ fun _ _ h => h).trans hLF3 fun a k h => hx.inRanges_old h
    have hsl3 : ESl M3 sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st) := by
      refine ESl.keep (ESl.keep hsl1 (fun a k ha => hF2.readLE a k ?_) (by omega)) (fun a k ha => hF3.readLE a k ?_)
        (by omega)
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hgcl ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact hgcb
    have hkfG : ArrKF R L st s.mem M3 := Or.inr (by simp only [stW, stCap] at q1 q3 ⊢; rw [q1, q3]; exact ⟨hpin, hapL⟩)
    have hFp : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 744), (sp + 760, sp + 848), (st, st + 24)]) := by
      refine MemFrame.trans hF12p hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, by omega, by omega⟩, ho.1, ho.2.2.2, by omega⟩
    obtain ⟨b1, hinv1, hb1⟩ := (P2Q.grow_eff (R := R) (b := b) (H := (HW (stLen s.mem st) lm)) (st := st) (M' := M3)
      (gc := growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))
      (L := L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) (g := g)
      (v := view R.rt (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + 20 * W lm) (stCap s.mem st))]) M3) hk'
      (by simp only [HW, StackNat.rnd]; omega) (by rw [show (20 * W lm + 3) / 4 * 4 = 20 * W lm by omega])).2 hinv3 q3
    refine KR M3 _ b1 hF hFp hLF (hrg3.trans (hrg2.trans hrg1)) hx hkfG q2 hcap3 hc3 ?_ (fun _ => ?_) hsl3
      hb1 hinv1 S3 e1 e2 e3 (e4.trans d4) ((e5.trans d9).trans c9) e6
      ((e7.trans d11).trans c11) e8
    · intro hc
      simp only [stW, stCap] at q1 q3 hc ⊢
      rw [q1, q3]
      exact ⟨hp8, Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
        by simp only; omega⟩, by rw [hF3.accessible]; exact hpacc, hp48⟩
    · simp only [stW, stCap] at q1 q3 ⊢
      rw [q1, q3]; exact List.mem_append_right _ (List.mem_singleton_self _)

end FvModexp.Arm64.P2W4
