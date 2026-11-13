import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsSNI

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsSN.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), big path: `qhat0 := stk.nat(B + 1)` (`fn + 0x104`) → the loop head (`H` at `j = m`)

`CALL (*stack).nat` (`StackNat.sumL` on `LibDrs`), then `MOVD R0, 336(RSP); MOVD R2, 184(RSP); MOVD R1, 176(RSP);
MOVD 192(RSP), R3; JMP` to the head `0x1ba504` (the back edge's `stk.restore(mark)` at `0x1ba4f0` is skipped).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

theorem tNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the `Cx` of an activation -/
@[reducible] def cOf (a : Args) (u1 t0 : Nat) (L1 : List (Nat × Nat)) : Cx :=
  ⟨a.Hq, a.b, a.L, a.W, a.qp.toNat, a.ql.toNat, a.qc.toNat, a.st.toNat, a.up.toNat, a.ul.toNat, a.uc.toNat, a.vp.toNat,
    a.vl.toNat, a.vc.toNat, a.d.toNat, u1, t0, L1⟩

/-- `(*stack).nat` as a summary in `LibDrs` -/
theorem snSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (Hq b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibDrs.program.link impl) (segAddr Extracted.program StackNat.fn)
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [st, k] ∧ StackNatX.PreQ R b L Hq 4208 24 st.toNat k.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        StackNatX.PostQ R b L Hq 4208 24 st.toNat k.toNat s s') := by
  have hS := StackNatX.sumQ impl hap R hgr hmc hwb Hq b L st k LibDrs.names (FvModexp.Arm64.Callees.sub_of_all (by decide))
  rw [← LibDrs.eq_only] at hS
  exact hS

/-- the fixed slots at the head from `AtN0`'s (pure) -/
theorem sl_init {c : Cx} {s P : State} {T S : Memory} {rs : List (Nat × Nat)}
    (hA : AtN0 s P c.qp c.ql c.qc c.st c.up c.u1 c.uc c.vp c.vl c.vc c.d) (hMF : MemFrame P.mem T rs) (hfo : FixOut s rs)
    (hM2 : MemFrame T S [(s.sp.toNat - 224, s.sp.toNat - 208), (s.sp.toNat - 64, s.sp.toNat - 56)])
    (h0 : 408 ≤ s.sp.toNat)
    (q1 : S.readLE (s.sp.toNat - 224) 8 = c.vl / 2 + 1) (q2 : S.readLE (s.sp.toNat - 216) 8 = c.vl / 2 + 1)
    (q3 : S.readLE (s.sp.toNat - 64) 8 = c.t0) : Sl c s S := by
  have hF := hA.fr
  have hS1 : Sl { c with t0 := c.t0 } s S := by
    have hP : ∀ x n, Outside x n rs → Outside x n [(s.sp.toNat - 224, s.sp.toNat - 208), (s.sp.toNat - 64, s.sp.toNat - 56)] →
        S.readLE x n = P.mem.readLE x n := fun x n h1 h2 => by rw [hM2.readLE x n h2, hMF.readLE x n h1]
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hfo
    have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N →
        Outside x n [(s.sp.toNat - 224, s.sp.toNat - 208), (s.sp.toNat - 64, s.sp.toNat - 56)] →
        S.readLE x n = P.mem.readLE x n := fun hA h1 h2 h3 => hP _ _ (hA.of_sub h1 h2) h3
    have oo : ∀ x n, (x + n ≤ s.sp.toNat - 224 ∨ s.sp.toNat - 208 ≤ x) → (x + n ≤ s.sp.toNat - 64 ∨ s.sp.toNat - 56 ≤ x) →
        Outside x n [(s.sp.toNat - 224, s.sp.toNat - 208), (s.sp.toNat - 64, s.sp.toNat - 56)] := by
      intro x n a b; simp only [outside_cons, outside_nil, and_true]; omega
    exact ⟨by rw [r o1 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hF.lr,
      by rw [r o1 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hF.fp,
      by rw [r o2 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dbit, q1, q2,
      by rw [r o3 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.mm,
      by rw [r o4 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.nn,
      by rw [r o4 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.ul',
      by rw [r o5 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.bb, q3,
      by rw [r o6 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dfn,
      by rw [r o6 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dst,
      by rw [r o6 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dn,
      by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dp,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s1,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s2,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s3,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s4,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s5,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s7,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s8,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s10,
      by rw [r o8 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s11⟩
  exact hS1

set_option maxHeartbeats 16000000 in
/-- **the head invariant at `j = m`** from the facts after the call (pure) -/
theorem head_mk {R : RtInv} {c : Cx} {s P S : State} {T : Memory} {rs : List (Nat × Nat)} {bk : Nat}
    (hcr : Cr R c s) (hev : Ev R c s c.L1 bk T) (hfp : Fp R c s c.L1 T (c.l1 s))
    (hkeep : ∀ x k, Held R c.L x k → Outside x k (win s c.W 96) → Apart x k c.st 24 →
      Apart x k (stW s.mem c.st + 8 * stLen s.mem c.st) (8 * (stCap s.mem c.st - stLen s.mem c.st)) →
      T.readLE x k = s.mem.readLE x k)
    (hA : AtN0 s P c.qp c.ql c.qc c.st c.up c.u1 c.uc c.vp c.vl c.vc c.d) (hMF : MemFrame P.mem T rs) (hfo : FixOut s rs)
    (hb1 : c.b - stkR c.Hq s.mem c.st + stkR c.Hq T c.st ≤ bk)
    (hpc : S.pc = BitVec.ofNat 64 head) (hsp : S.sp = s.sp - 400#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 408#64) (h18 : S.regs 18 = s.regs 18) (h0 : S.regs 0 = BitVec.ofNat 64 c.t0)
    (h1 : S.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h2 : S.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h3 : S.regs 3 = BitVec.ofNat 64 (c.u1 - c.vl))
    (hM2 : MemFrame T S.mem [(s.sp.toNat - 224, s.sp.toNat - 208), (s.sp.toNat - 64, s.sp.toNat - 56)])
    (hreg : S.mem.regions = T.regions)
    (q1 : S.mem.readLE (s.sp.toNat - 224) 8 = c.vl / 2 + 1) (q2 : S.mem.readLE (s.sp.toNat - 216) 8 = c.vl / 2 + 1)
    (q3 : S.mem.readLE (s.sp.toNat - 64) 8 = c.t0) :
    H R c s c.L1 bk S (c.u1 - c.vl) := by
  have hW := hcr.hW; have := drsW_ge c.vl
  have hpre := hcr.pre
  obtain ⟨hce, -, -, -, -, -, -, -, -, hv2, -, htop, hq0, -, ⟨-, -, hqh, hqw, -⟩, ⟨-, -, huh, huw, -⟩,
    ⟨-, -, hvh, hvw, -, -, -⟩, -, -, -, -, ⟨-, hc0, -⟩, ⟨hqs, hqf⟩, ⟨hus, huf⟩, ⟨hvs, hvf⟩, -, -, -, -, hcb, -⟩ := hpre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hfw : MemFrame T S.mem (fw s) := hM2.mono fun x k ho => by
    simp only [fw, winA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hk2 : ∀ x k, Held R c.L x k → Outside x k (win s c.W 96) → Apart x k c.st 24 →
      Apart x k (stW s.mem c.st + 8 * stLen s.mem c.st) (8 * (stCap s.mem c.st - stLen s.mem c.st)) →
      S.mem.readLE x k = s.mem.readLE x k := fun x k a b c d => by
    rw [hfw.readLE x k (fw_out (by omega) b)]; exact hkeep x k a b c d
  have hsub : ∀ {x k : Nat}, c.up ≤ x → x + k ≤ c.up + 8 * c.ul → S.mem.readLE x k = s.mem.readLE x k :=
    fun h1 h2 => hk2 _ _ (huh.sub h1 h2) (huw.of_sub h1 h2) (by unfold Apart at hus ⊢; omega)
      (by unfold Apart at huf ⊢; omega)
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have eq : natVal S.mem c.qp c.ql = 0 := by
    show S.mem.readLE c.qp (8 * c.ql) = 0
    rw [hk2 _ _ hqh hqw hqs hqf]; exact hq0
  have eu : natVal S.mem c.up c.u1 = natVal s.mem c.up c.u1 := hsub (Nat.le_refl _) (by omega)
  refine ⟨hpc, hsp, h28, h29, h18, h0, h1, h2, h3, hcr, hev.own hcr hfw hreg, hfp.own hcr hfw,
    sl_init hA hMF hfo hM2 (by omega) q1 q2 q3, li_init (by omega) hvu htop eq eu _,
    hk2 _ _ hvh hvw hvs hvf, hsub (by omega) (by omega), ?_⟩
  have hsto : Outside c.st 24 (win s c.W 96) := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hcS : stCap S.mem c.st = stCap T c.st := hfw.readLE _ _ (fw_out (by omega) (hsto.of_sub (by omega) (by omega)))
  exact bud_init (R := R) (M := S.mem) hcb.2 hcr.h40 hvu hu1 (by rw [stkR_congr hcS]; exact hb1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`qhat0 := stk.nat(B + 1)`, then to the loop head** with `j = m` -/
theorem snH (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (a : Args) (s : State) (hE : Entry a s)
    (hpre : DrsPreW R a.b a.L a.Hq (drsCQ a.ul.toNat a.vl.toNat) a.W a.qp.toNat a.ql.toNat
      a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat a.vp.toNat a.vl.toNat a.vc.toNat s)
    (hW : drsW a.vl.toNat ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtN0 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp.toNat a.vl.toNat
      a.vc.toNat a.d.toNat)
    (hle : ul' ≤ a.ul.toNat) (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat)
    (hN : NatNorm s.mem a.up.toNat ul') (h40 : 40 ≤ a.vl.toNat) (hvu : a.vl.toNat ≤ ul') (Q : State → Prop)
    (k : ∀ t0 L1 Lk bk S, H R (cOf a ul' t0 L1) s Lk bk S (ul' - a.vl.toNat) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q := by
  have hWg := drsW_ge a.vl.toNat
  have hpre' := hpre
  obtain ⟨hce, -, -, -, -, -, huc, -, hvc, -, ⟨hvl9, -⟩, -, -, -, -, -, -, -, -, -, -, ⟨hstl, -⟩, -⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', -, hw⟩, -⟩ := hce
  have hF := hA.fr
  have hpc := hA.pc; have hr0 := hA.r0; have hr1 := hA.r1
  have hsp := hF.sp; have h28 := hF.r28; have h29 := hF.r29; have h18 := hF.r18
  have hn64 : a.vl.toNat / 2 + 1 < 2 ^ 64 := by omega
  janus_run until [segAddr Extracted.program StackNat.fn]
  refine ReachesRet.call_regions (snSum impl hap R hgr hmc hwb a.Hq a.b a.L a.st (BitVec.ofNat 64 (a.vl.toNat / 2 + 1)))
    rfl ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 0x1ba4a8 : BitVec 64).toNat = 0x1ba4a8 := by decide
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom, setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    exact ⟨by rw [hr0, bv_ofNat_toNat], by rw [hr1], trivial⟩
  case pre =>
    rw [tNat hn64]
    refine sn_pre hpre (by omega) ?_ ?_ ?_ ?_
    · first | exact hA.mf | (rw [hm]; exact hA.mf)
    · first | exact hsp | rfl
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [h28]
    · first | exact hF.reg | (rw [hm]; exact hF.reg)
  rw [tNat hn64] at hq
  obtain ⟨hq0, hq1, hq2, L', b', ⟨hext, hbud, hinv⟩, hok, hlen, hsame, hgrow, hMF, hLF, hmem⟩ := hq
  have hsto : Outside a.st.toNat 24 (win s a.W 96) := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hfw : Outside (stW s.mem a.st.toNat + 8 * stLen s.mem a.st.toNat)
      (8 * (stCap s.mem a.st.toNat - stLen s.mem a.st.toNat)) (win s a.W 96) :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : Outside a.st.toNat 24 (fw s) := by
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have eW : stW P.mem a.st.toNat = stW s.mem a.st.toNat := hF.fr.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eL : stLen P.mem a.st.toNat = stLen s.mem a.st.toNat := hF.fr.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap P.mem a.st.toNat = stCap s.mem a.st.toNat := hF.fr.readLE _ _ (hst.of_sub (by omega) (by omega))
  have hfo : ∀ X : State, X.sp = s.sp - 400#64 → FixOut s (R.rt ++ winA X 4208 24 ++ stkWs P.mem a.st.toNat) := by
    intro X hX
    have hout := hpre.1.2.2.2.1
    refine fixOut_callee hout (by omega) (by omega) ?_ (by omega) ?_
    · rw [hX, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    · simp only [stkWs, eW, eL, eC]
      simp only [win, outside_cons, outside_nil, and_true] at hsto hfw
      simp only [FixOut, outside_cons, outside_nil, and_true]; omega
  have hmmT : T.mem.readLE (s.sp.toNat - 208) 8 = ul' - a.vl.toNat := by
    rw [hMF.readLE _ _ ((hfo _ rfl).2.2.1.of_sub (by omega) (by omega))]; exact hA.mm
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hMF.accessible, hF.fr.accessible]
    exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hTpc : T.pc = BitVec.ofNat 64 0x1ba4a8 := by rw [hT]; simp only [setReg_apply, ↓reduceIte]
  have hTsp : T.sp = s.sp - 400#64 := f1
  have hT0 := hq0 (by omega)
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hreg : T.mem.regions = s.mem.regions := by rw [hrg]; exact hF.reg
  have hinv' : R.inv b' L' (s.regs 28).toNat (view R.rt L' T.mem) := by
    have := hinv; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at this; rw [h28] at this; exact this
  obtain ⟨hcr, hev, hfp, hkeep⟩ := hd_mem (c := cOf a ul' (stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat) L')
    (T := T.mem) (bk := b') hpre hE.1 hE.2.1 hW h40 hvu hle hU hN hMF hLF hA.mf rfl rfl hext hinv' hok hlen hsame hgrow
    hmem hreg
  have hT0' : T.regs 0 = BitVec.ofNat 64 (stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat) := by
    rw [hT0]; show BitVec.ofNat 64 (stW T.mem a.st.toNat + 8 * stLen P.mem a.st.toNat) = _; rw [eL]
  have hb1 : a.b - stkR a.Hq s.mem a.st.toNat + stkR a.Hq T.mem a.st.toNat ≤ b' := by
    have := hbud; rw [stkR_congr eC] at this; exact this
  clear hpc hr0 hr1 hT0 hq0 hext hinv hinv' hok hlen hsame hgrow hLF hmem hbud hpre hrg hT
  janus_run [hmmT] until [head]
  refine k (stW T.mem a.st.toNat + 8 * stLen s.mem a.st.toNat) L' L' b' _ ?_
  refine head_mk hcr hev hfp hkeep hA hMF (hfo _ rfl) hb1 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus_frame) (by janus_simp)
    ?_ ?_ ?_
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [f2]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [f3]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h29
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [f4]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hT0'
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hq1
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hq2
  · simp only [setReg_apply, ↓reduceIte, cOf]
  all_goals dsimp only
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, Nat.mod_eq_of_lt]
    have := hcr.t048; simp only [cOf] at this; omega

end FvModexp.Arm64.Q.DivRec
