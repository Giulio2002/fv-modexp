import FvModexp.Proofs.Arm64.Exp.W4EnA
import FvModexp.Proofs.Arm64.Exp.W4EnG2
import FvModexp.Proofs.Arm64.Exp.W4EnJ
import FvModexp.Proofs.Arm64.Exp.W4EnX

/-!
# window-4 (arm64): from the function's entry to its `RET` (= `enA` + (`enG2`) + `enJn` + `atXnE`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

open FvModexp.Arm64.W4Pro (XnPost xjBud xnBudA xnBudAC reaches_mono isReturn_mono)

theorem ESl.keep {M1 M3 : Memory} {sp st : Nat} {r29 : BitVec 64} {ret zp zc xp xl xc yp ylen mp n mc len0 : Nat}
    (h : ESl M1 sp st r29 ret zp zc xp xl xc yp ylen mp n mc len0)
    (hk : ∀ a, (sp - 8 ≤ a ∧ a + 8 ≤ sp + 8 ∨ sp + 840 ≤ a ∧ a + 8 ≤ sp + 1040) → M3.readLE a 8 = M1.readLE a 8)
    (hsp : 8 ≤ sp) : ESl M3 sp st r29 ret zp zc xp xl xc yp ylen mp n mc len0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := h
  exact ⟨by rw [hk _ (by omega)]; exact a1, by rw [hk _ (by omega)]; exact a2, by rw [hk _ (by omega)]; exact a3,
    by rw [hk _ (by omega)]; exact a4, by rw [hk _ (by omega)]; exact a5, by rw [hk _ (by omega)]; exact a6,
    by rw [hk _ (by omega)]; exact a7, by rw [hk _ (by omega)]; exact a8, by rw [hk _ (by omega)]; exact a9,
    by rw [hk _ (by omega)]; exact a10, by rw [hk _ (by omega)]; exact a11, by rw [hk _ (by omega)]; exact a12,
    by rw [hk _ (by omega)]; exact a13, by rw [hk _ (by omega)]; exact a14, by rw [hk _ (by omega)]; exact a15,
    by rw [hk _ (by omega)]; exact a16, by rw [hk _ (by omega)]; exact a17⟩

/-- what window-4 guarantees from its entry (memory `s.mem`) on: the memory `M` at `xnE` (after the inline
`stk.reserve(23n)`) with its frame from `s.mem`, and `XnPost` anchored at `M` -/
@[reducible] def EnPost (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (K g sp st zp zc xp xl yp ylen mp n mc costD : Nat) (s s' : State) : Prop :=
  ∃ Xv', Xv' % s.mem.readLE mp (8 * n) = s.mem.readLE xp (8 * xl) % s.mem.readLE mp (8 * n) ∧ Xv' < Exp.B ^ n ∧
  ∃ (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [(sp - K, sp + 920), (sp + 936, sp + 1040), (st, st + 24)]) ∧
    LiveFrame s.mem M L [(st, st + 24)] ∧ LiveExt R L L1 ∧ b - stackNatCost (stLen s.mem st) (23 * n) ≤ b1 ∧
    ArrKF R L st s.mem M ∧ stLen M st = stLen s.mem st + StackNat.rnd (23 * n) ∧ stLen M st ≤ stCap M st ∧
    XnPost R L1 K (b1 - W4Pro.xnPre n costD (stLen s.mem st + StackNat.rnd (23 * n)) (xl - n + 1)) M g sp n mp mc
      (s.mem.readLE mp (8 * n)) Xv' yp ylen (s.mem.readLE yp (8 * ylen)) (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc
      st (stLen s.mem st) (stLen s.mem st + StackNat.rnd (23 * n)) (s.regs 18) (s.regs 29) s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **window-4 from its entry to its `RET`** (arm64): prologue, defer record, the inline `stk.reserve(23n)`, then the
rest of the function (`W4Pro.xnStep`). -/
theorem enStep (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (hgr : GrowsliceLiveContract (LibExp.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibExp.program.link impl) mcE 4096 R)
    (hwb : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibExp.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg34.name = false)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp ylen mp n mc : Nat) (s : State)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1) (hM1 : 1 < s.mem.readLE mp (8 * n))
    (hslen : stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl +
      StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcs : W4Pro.DivCosts costF costD n xl (stLen s.mem st + StackNat.rnd (23 * n)))
    (hbC : stackNatCost (stLen s.mem st) (23 * n) + xjBud n costD (stLen s.mem st + StackNat.rnd (23 * n)) ≤ b)
    (hbB : stackNatCost (stLen s.mem st) (23 * n) + (stackNatCost (stLen s.mem st + StackNat.rnd (23 * n)) n +
      xjBud n costD (stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd n)) ≤ b)
    (hbA : stackNatCost (stLen s.mem st) (23 * n) +
      xnBudA n costD (stLen s.mem st + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b)
    (hbAC : stackNatCost (stLen s.mem st) (23 * n) +
      xnBudAC n costD (stLen s.mem st + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b)
    (hbP : stackNatCost (stLen s.mem st) (23 * n) +
      W4Pro.xnPre n costD (stLen s.mem st + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 ylen)
    (h10 : s.regs 10 = BitVec.ofNat 64 mp) (h11 : s.regs 11 = BitVec.ofNat 64 n)
    (h12 : s.regs 12 = BitVec.ofNat 64 mc) (h30 : s.regs 30 = BitVec.ofNat 64 ret) :
    Reaches ((LibExp.program.link impl).withExit ret) s
      (IsReturn (EnPost R b L K g sp st zp zc xp xl yp ylen mp n mc costD s)) := by
  have hP' := hP
  obtain ⟨he, hK20, hgl, hro, hty, hn, hn128, hmc0, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl',
    hxO, hxa, hx48, hxN, hxl, hxl', hxp, hxc, hzp, hzc, hz, hgO, hsok, hstw, hstg, harr, hwbf, hwbA, hstf, hl16,
    hinv⟩ := hP'
  have he' := he
  obtain ⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩ := he'
  have hsok' := hsok
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok'
  have hout : Outside (sp - K) (K + 1040) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1040 - (sp - K) = K + 1040 by omega] at this
  unfold Apart at hstw hstg
  have hr48 := hret.user
  have hrn : StackNat.rnd (23 * n) ≤ 23 * n + 3 := by simp only [StackNat.rnd]; omega
  have hrn0 : 0 < StackNat.rnd (23 * n) := by simp only [StackNat.rnd]; omega
  have e1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by apply BitVec.eq_of_toNat_eq; simp
  have e9 : s.regs 9 = BitVec.ofNat 64 (s.regs 9).toNat := by apply BitVec.eq_of_toNat_eq; simp
  have hok : R.ok wbE [2] := by rw [← wbE_eq]; exact hsv.2.2.2.2.2.1 _
  refine enA impl ret hret _ sp g st zp (s.regs 1).toNat zc xp xl xc yp ylen (s.regs 9).toNat mp n mc ret
    (stW s.mem st) (stLen s.mem st) (stCap s.mem st) (s.regs 29) s.mem hal (by omega) hsp2
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) (Memory.accessible_weaken _ k3) k4
    (by omega) rfl rfl rfl (by omega) k7 hn128 hr48 hzp (BitVec.isLt _) (by omega) hxp (by omega) hxc (by omega)
    (by omega) (BitVec.isLt _) (by omega) (by omega) s hpc hs1 h0 e1 h2 h3 h4 h5 h6 h7 h8 e9 h10 h11 h12 hs28 rfl h30
    rfl ?KJ ?KG
  case KJ =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 hF1p hrg1 hsl1
    have hF1 : MemFrame s.mem M1 [(sp - 8, sp + 1040)] := hF1p.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hinvM1 : R.inv b L g (view R.rt L M1) := RtInv.inv_frame hF1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hout.of_sub (by omega) (by omega)) hinv
    refine enJn impl R hwb ret hret _ b L g sp st (stW s.mem st) (stLen s.mem st) (stCap s.mem st) n M1 hal (by omega)
      hsp2 (by rw [hF1.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega))
      (LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega)) (LiveSep.sub_win hLs (by omega) (by omega))
      (by rw [hF1.accessible]; exact k3) k4 k2 (by omega) (by rw [hF1.accessible]; exact hwbf) hwbA hok hinvM1
      (by omega) hk k7 (Memory.readLE_lt _ _ _) (by omega) hn128 S1 c1 c2 c3 c10 c11 c12 c13 c15 c17 ?_
    intro S3 M3 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 1040), (st, st + 24)]) := by
      refine MemFrame.trans hF1 hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨by omega, ho.1, ho.2.2, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] :=
      (LiveFrame.of_win hF1 (LiveSep.sub_win hLs (by omega) (by omega))).trans hLF3 fun _ _ h => h
    have hFp : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 920), (sp + 936, sp + 1040), (st, st + 24)]) := by
      refine MemFrame.trans hF1p hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨by omega, by omega⟩, ho.1, ho.2.2.2, by omega⟩
    have hsl3 : ESl M3 sp st (s.regs 29) ret zp zc xp xl xc yp ylen mp n mc (stLen s.mem st) := by
      refine ESl.keep hsl1 (fun a ha => hF3.readLE a 8 ?_) (by omega)
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hk ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact k7
    refine reaches_mono (atXnE impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL ret
      hret b L K g sp
      st zp zc xp xl xc yp ylen mp n mc s (s.regs 18) (s.regs 29) (BitVec.ofNat 64 (sp - 8)) hP hKD hKL hMo hM1 hslen hcs
      hbC hbB hbA hbAC hbP M3 L b hF hLF (hrg3.trans hrg1) (LiveExt.refl R L) (Or.inl ⟨q1, q3⟩) q2 hcap3 hc3 ?_ hsl3
      (by omega) hinv3 S3 d1 d2 d3
      (d4.trans c4) (d5.trans c5) (d6.trans c6) (d7.trans c7) (d8.trans c8) (d9.trans c9) (d10.trans c14) d11
      (d12.trans c16) d13)
      (isReturn_mono fun s' ⟨Xv', h1, h1', h2⟩ => ⟨Xv', h1, h1', M3, L, b, hFp, hLF, LiveExt.refl R L, Nat.sub_le _ _,
        Or.inl ⟨q1, q3⟩, q2, hcap3, h2⟩)
    intro hc
    simp only [stW, stCap] at q1 q3 hc ⊢
    rw [q3] at hc; rw [q1, q3]
    obtain ⟨a1, a2, a3, a4⟩ := k5 hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  case KG =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hF1p hrg1 hsl1 q328 q192 q216 q320
    have hF1 : MemFrame s.mem M1 [(sp - 8, sp + 1040)] := hF1p.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hsl1' := hsl1
    obtain ⟨-, -, -, -, -, -, -, -, a9, a10, a11, a12, -, a14, a15, a16, -⟩ := hsl1'
    have hcostG : 8 * growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st) ≤
        stackNatCost (stLen s.mem st) (23 * n) := growRound_le_cost _ _ _ hk
    have hgcl := le_growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st)
    have hgcb := growCap_lt (stLen s.mem st) (23 * n) (stCap s.mem st) hk (by omega)
    refine enG2 impl R hgr hmc ret hret _ b L g sp K st xp xl xc ylen mp n (stW s.mem st) (stLen s.mem st)
      (stCap s.mem st) s he hk hn128 (by omega) (Memory.readLE_lt _ _ _) (fun hc => ?_) (by omega) hinv S1 M1 c1 c2 c3
      c4 c5 c6 c7 c8 c10 c12 hF1 q328 q192 q216 q320 a9 a10 a11 a12 a14 a15 a16 ?_
    · obtain ⟨-, -, a3, a4⟩ := k5 hc
      exact ⟨a4, Memory.accessible_weaken _ a3⟩
    intro S2 M2 p gc d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 hgc hpin hapL hp8 hp48 hpacc hF2 hLF2
      hrg2 hinv2
    subst hgc
    have hx : LiveExt R L (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st))]) :=
      ⟨[(p, p + 8 * growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st))], rfl, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]; exact ⟨hpin, hapL⟩,
        List.pairwise_singleton _ _⟩
    have hF12 : MemFrame s.mem M2 (R.rt ++ [(sp - K, sp + 1040)]) := by
      refine MemFrame.trans hF1 hF2 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨by omega, ho.1, by omega, by omega⟩
    have hinvM2 := hinv2
    have hF12p : MemFrame s.mem M2 (R.rt ++ [(sp - K, sp + 920), (sp + 936, sp + 1040)]) := by
      refine MemFrame.trans hF1p hF2 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨by omega, by omega⟩, ho.1, by omega, by omega⟩
    refine enJn impl R hwb ret hret _ (b - 8 * growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st))
      (L ++ [(p, p + 8 * growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st))]) g sp st p
      (stLen s.mem st) (growCap8 (stLen s.mem st + StackNat.rnd (23 * n)) (stCap s.mem st)) n M2 hal (by omega)
      hsp2 (by rw [hF12.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega))
      (LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega))
      (hx.liveSep (LiveSep.sub_win hLs (by omega) (by omega)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        exact hout.of_sub (by omega) (by omega))
      (by rw [hF12.accessible]; exact k3) k4 (hx.held k2) (by omega) (by rw [hF12.accessible]; exact hwbf) hwbA hok
      hinvM2 (by omega) hgcl hgcb (by omega) (by omega) hn128 S2 d1 d2 d3 d10 d11 d12 d13 d15 d17 ?_
    intro S3 M3 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 1040), (st, st + 24)]) := by
      refine MemFrame.trans hF12 hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, ho.2.1⟩, ho.1, ho.2.2, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] := by
      refine ((LiveFrame.of_win hF1 (LiveSep.sub_win hLs (by omega) (by omega))).trans
        ⟨fun a k hin _ => hLF2.readLE a k hin trivial⟩ fun _ _ h => h).trans hLF3 fun a k h => hx.inRanges_old h
    have hsl3 : ESl M3 sp st (s.regs 29) ret zp zc xp xl xc yp ylen mp n mc (stLen s.mem st) := by
      refine ESl.keep (ESl.keep hsl1 (fun a ha => hF2.readLE a 8 ?_) (by omega)) (fun a ha => hF3.readLE a 8 ?_)
        (by omega)
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hgcl ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact hgcb
    have hkfG : ArrKF R L st s.mem M3 := Or.inr (by simp only [stW, stCap] at q1 q3 ⊢; rw [q1, q3]; exact ⟨hpin, hapL⟩)
    have hFp : MemFrame s.mem M3 (R.rt ++ [(sp - K, sp + 920), (sp + 936, sp + 1040), (st, st + 24)]) := by
      refine MemFrame.trans hF12p hF3 fun a k ho => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1, by omega, by omega⟩, ho.1, ho.2.2.2, by omega⟩
    refine reaches_mono (atXnE impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL ret
      hret b L K g sp
      st zp zc xp xl xc yp ylen mp n mc s (s.regs 18) (s.regs 29) (BitVec.ofNat 64 (sp - 8)) hP hKD hKL hMo hM1 hslen hcs
      hbC hbB hbA hbAC hbP M3 _ _ hF hLF (hrg3.trans (hrg2.trans hrg1)) hx hkfG q2 hcap3 hc3 ?_ hsl3
      (by omega) hinv3 S3 e1 e2 e3 (e4.trans d4) (e5.trans d5) (e6.trans d6) (e7.trans d7) (e8.trans d8) (e9.trans d9)
      ((e10.trans d14).trans c9) e11 ((e12.trans d16).trans c11) e13)
      (isReturn_mono fun s' ⟨Xv', h1, h1', h2⟩ => ⟨Xv', h1, h1', M3, _, _, hFp, hLF, hx, Nat.sub_le_sub_left hcostG _, hkfG, q2, hcap3, h2⟩)
    · intro hc
      simp only [stW, stCap] at q1 q3 hc ⊢
      rw [q1, q3]
      exact ⟨hp8, Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
        by simp only; omega⟩, by rw [hF3.accessible]; exact hpacc, hp48⟩

end FvModexp.Arm64.W4En
