import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2XnJ
import FvModexp.Proofs.Arm64.Exp.W2XnD

/-!
# window-2 prologue (arm64): path A of the `x` normalisation, `_, x = stk.nat(len x - n + 1).div(stk, stk.nat(n), x, m)`
(nat.go:1377-1379), composed with the join (`xnJStep`)

* `CtxB.addEx`/`CtxB.dropEx`: the scratch quotient `q` (possibly left in an old stack array by the second `stk.nat`) is
  an extra range of the context while the division runs;
* `rem_xin`: the remainder (the old `z2` buffer or a fresh object) satisfies `XIn` at the stack level after the division.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
/-- the threshold globals as an object of the context (asm s16 DivHyp addendum) -/
theorem CtxB.ga {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) : Obj R L sp K st l0 ex M RunIface.gA 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hga, -⟩ := h
  exact hga

theorem CtxB.stnz {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) : st ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfe, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact FinEnv.stnz hfe

set_option maxRecDepth 20000 in
/-- the stack header's separation from the guard word, the write-barrier flag and the free part (asm s18, `DivPre`) -/
theorem CtxB.hdr {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) :
    Apart st 24 (g + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfe, -, -, hsok, -, hl0, -, -, -, -,
    hsu, -, -, hwb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := hfe
  have hlc := hsok.2.2.2.2.2.1
  refine ⟨hg, hwb, ?_⟩
  simp only [stUp, Apart] at hsu ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxB.addEx {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {e : Nat × Nat} {M : Memory} (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    (he : (stW M st + 8 * l0 ≤ e.1 ∧ e.1 + e.2 ≤ stW M st + 8 * stCap M st)) :
    CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 (e :: ex) M := by
  obtain ⟨he', hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r728, r736, r744, r664, r648, r712, r704, r672⟩ := h
  exact ⟨he', hce, hK, hK20, hn, hn128, hmc, hmc', hm, obj_addEx hmO he, hmV, hnm, hy,
    obj_addEx hyO he, hY, hyi, hyi0, hyl, hyl', hzc,
    fun h2 => ⟨(hz h2).1, (hz h2).2.1, obj_addEx (hz h2).2.2.1 he, (hz h2).2.2.2.1, (hz h2).2.2.2.2⟩,
    hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, obj_addEx hgO he, hstwb, hro, hty,
    r728, r736, r744, r664, r648, r712, r704, r672⟩

theorem obj_drop {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 a k : Nat} {ex : List (Nat × Nat)} {e : Nat × Nat}
    {M : Memory} (h : Obj R L sp K st l0 (e :: ex) M a k) : Obj R L sp K st l0 ex M a k :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun e' he' => h.2.2.2.2 e' (List.mem_cons_of_mem _ he')⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxB.dropEx {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {e : Nat × Nat} {M : Memory} (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 (e :: ex) M) :
    CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M := by
  obtain ⟨he', hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r728, r736, r744, r664, r648, r712, r704, r672⟩ := h
  exact ⟨he', hce, hK, hK20, hn, hn128, hmc, hmc', hm, obj_drop hmO, hmV, hnm, hy,
    obj_drop hyO, hY, hyi, hyi0, hyl, hyl', hzc,
    fun h2 => ⟨(hz h2).1, (hz h2).2.1, obj_drop (hz h2).2.2.1, (hz h2).2.2.2.1, (hz h2).2.2.2.2⟩,
    hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, obj_drop hgO, hstwb, hro, hty,
    r728, r736, r744, r664, r648, r712, r704, r672⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the remainder of `x mod m` is an `XIn` operand at the stack level after the division -/
theorem rem_xin {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K st l0 n b b' costD stkD qp qc z2p xp xl mp Mv r rl rc : Nat} {M M' : Memory}
    (hrt : Outside (sp - K) (K + 752) R.rt) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hsu : Apart st 24 (stUp M st l0).1 (stUp M st l0).2)
    (hsok : StkOK M R L st) (hcap : 0 < stCap M st) (harr : AW sp K (stW M st) (8 * stCap M st))
    (hz2 : stW M st + 8 * l0 ≤ z2p ∧ z2p + 8 * n ≤ stW M st + 8 * stLen M st) (hn : 0 < n)
    (hmv : M.readLE mp (8 * n) = Mv) (hmB : Mv < Exp.B ^ n) (hM0 : 0 < Mv)
    (hD : DvPostG R b costD L L' b' g sp stkD st qp qc z2p n xp xl mp n M M' r rl rc) (hcap' : 0 < stCap M' st) :
    XIn R L' sp K st (stLen M' st) M' r rl rc ∧ M'.readLE r (8 * rl) = M.readLE xp (8 * xl) % Mv ∧ rl ≤ n ∧
      r < 2 ^ 64 := by
  obtain ⟨⟨hv, hN, hlc, hc40, hlive, hor⟩, hx, -, -, ⟨⟨hsok', hlen', hst'⟩, -⟩, hfr, -, -, -⟩ := hD
  have hsok0 := hsok
  obtain ⟨-, -, -, -, hla, hlcM, -⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hla hcap
  have hval : M'.readLE r (8 * rl) = M.readLE xp (8 * xl) % Mv := by
    have := hv; simp only [natVal] at this; rw [this, hmv]
  have hBn : Exp.B ^ n = 2 ^ (64 * n) := by
    rw [Exp.B_eq, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, ← Nat.pow_mul]
  have hrln : rl ≤ n := norm_len_le hN (by rw [hval, ← hBn]; exact Nat.lt_trans (Nat.mod_lt _ hM0) hmB)
  have hrc0 : 0 < rc := by rcases hor with ⟨-, e⟩ | ⟨h1, -⟩ <;> omega
  obtain ⟨r8, rH, racc, r48⟩ := hlive hrc0
  refine ⟨⟨hlc, hrc0, hc40, M'.accessible_sub racc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _), r48, ?_⟩, hval, hrln,
    by omega⟩
  simp only [AW] at harr
  rcases hor with ⟨e1, e2⟩ | ⟨-, hin, hap⟩
  · -- the old `z2` buffer
    subst e1 e2
    refine ⟨rH, by simp only [AW, Apart] at harr ⊢; omega, by simp only [stUp, Apart] at hsu ⊢; omega, ?_,
      fun e he => by simp at he⟩
    rcases hst' with ⟨w1, w2⟩ | ⟨hin, hap⟩
    · simp only [stUp, Apart]; rw [w1, w2, hlen']; omega
    · have := apart_fresh (a := r) (n := 8 * rc) hin hap (held_sub lah (by omega) (by omega))
      simp only [stUp, Apart] at this ⊢; omega
  · -- a fresh object
    have hne : ¬ (r = z2p ∧ rc = n) := by
      intro ⟨e1, e2⟩
      rw [e1, e2] at hin hap
      have := apart_fresh (a := z2p) (n := 8 * n) hin hap (held_sub lah (by omega) (by omega))
      unfold Apart at this; omega
    have h1 := hfr hne hrc0 hcap'
    have h2 := out_inR hrt hin
    have h3 := apart_fresh hin hap hsth
    refine ⟨rH, by simp only [AW, Apart]; omega, by unfold Apart at h3 ⊢; omega, ?_, fun e he => by simp at he⟩
    have := hsok'.2.2.2.2.2.1
    simp only [stUp, Apart] at h1 ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path A from the return of `z2 := stk.nat(n)` (`aSn2Ret`) to the function's `RET`: the division, `x := r`, the join -/
theorem xnA2K (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg35.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xc qp k : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [(qp, 8 * k)] M)
    (hlen : stLen M st = l0 + StackNat.rnd k + StackNat.rnd n)
    (hk0 : 0 < k) (hk40 : k < 2 ^ 40) (hq8 : qp % 8 = 0) (hqH : Held R L qp (8 * k))
    (hqa : M.accessible qp (8 * k) true = true) (hq48 : qp + 8 * k ≤ 2 ^ 48) (hqW : AW sp K qp (8 * k))
    (hqG : Apart qp (8 * k) (g + 16) 8) (hqS : Apart qp (8 * k) st 24)
    (hqB : (stW M st + 8 * l0 ≤ qp ∧ qp + 8 * k ≤ stW M st + 8 * stLen M st) ∨
      Apart qp (8 * k) (stW M st) (8 * stCap M st))
    (hqz : Apart qp (8 * k) (stW M st + 8 * (l0 + StackNat.rnd k)) (8 * n))
    (hxO : Obj R L sp K st l0 [(qp, 8 * k)] M xp (8 * xl)) (hxa : M.accessible xp (8 * xl) false = true)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxN : NatNorm M xp xl) (hxl : n < xl) (hxl' : xl ≤ 128) (hxc : xc < 2 ^ 64)
    (hxv : M.readLE xp (8 * xl) = Xv)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd k + StackNat.rnd n + 16 * xl + StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤
      2 ^ 16)
    (hcX : costF (l0 + StackNat.rnd k + StackNat.rnd n) xl n ≤ costD)
    (hcRB : costF (l0 + StackNat.rnd k + StackNat.rnd n + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hcRC : costF (l0 + StackNat.rnd k + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbC : costD + xjBud n costD (l0 + StackNat.rnd k + StackNat.rnd n) ≤ b)
    (hbB : costD + (stackNatCost (l0 + StackNat.rnd k + StackNat.rnd n) n +
      xjBud n costD (l0 + StackNat.rnd k + StackNat.rnd n + StackNat.rnd n)) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (r616 : M.readLE (sp + 616) 8 = qp) (r328 : M.readLE (sp + 328) 8 = k) (r320 : M.readLE (sp + 320) 8 = k)
    (r680 : M.readLE (sp + 680) 8 = xp) (r688 : M.readLE (sp + 688) 8 = xl) (r696 : M.readLE (sp + 696) 8 = xc)
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbAC : bA + (costD + xjBudA n costD (l0 + StackNat.rnd k + StackNat.rnd n)) ≤ b)
    (hbAB : bA + (costD + (stackNatCost (l0 + StackNat.rnd k + StackNat.rnd n) n +
      xjBudA n costD (l0 + StackNat.rnd k + StackNat.rnd n + StackNat.rnd n))) ≤ b)
    (hl0A : stLen M0 st ≤ l0) (hexA : ALoc R L0 st M0 (qp, 8 * k))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 aSn2Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 (stW M st + 8 * (l0 + StackNat.rnd k))) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h2 : S.regs 2 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (XnPost R L0 K bA M0 g sp n mp mc Mv (Xv % Mv) yp ylen Y yi zp zc st n0 l0 r18 r29)) := by
  have hB0 := hB
  obtain ⟨he, hce, hK, -, hn, hn128, -, hmc', hm, hmO, hmV, hnm, -, -, -, -, -, -, -,
    -, -, -, hsth, hstw, hsok, -, -, hcap, harr, -, -, hsu, hgl, -, -, -, -,
    r728, r736, r744, -, -, -, -, r672⟩ := hB0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hsok0 := hsok
  obtain ⟨-, -, -, hst48, hlive, hlc, -⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  have harr0 := harr hcap
  have hrn : n ≤ StackNat.rnd n := by simp only [StackNat.rnd]; omega
  have hrk : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega
  have hr4 : StackNat.rnd k % 4 = 0 := by simp only [StackNat.rnd]; omega
  have hzin : stW M st + 8 * l0 ≤ stW M st + 8 * (l0 + StackNat.rnd k) ∧
      stW M st + 8 * (l0 + StackNat.rnd k) + 8 * n ≤ stW M st + 8 * stLen M st := by omega
  refine xnA2 impl ret hret _ sp st qp k k xp xl xc mp n mc M hal (by omega) hA
    (M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) r672 r616 r328 r320 r680 r688 r696 r728 r736 r744
    S hpc hsp hmem (fun S4 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 => ?_)
  have hRA : RetAddr ((Extracted.program.onlySegments nsD).link impl) aDivRet :=
    CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := nsD)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hnsW 131
      (by decide) (by decide) (by decide)
  have hpre : DvPreG R b costF costD L g sp K stkD st qp k k (stW M st + 8 * (l0 + StackNat.rnd k)) n n xp xl mp n M := by
    obtain ⟨a1, a2⟩ := harr0
    have hga := CtxB.ga hB
    have hgu := hga.2.2.2.1
    obtain ⟨o1, o2, o3, o4, o5⟩ := hxO
    obtain ⟨m1, m2, m3, m4, m5⟩ := hmO
    have ox := o5 _ (List.mem_cons_self ..)
    have om := m5 _ (List.mem_cons_self ..)
    refine ⟨hce, hKD, hserv, hgl, hn128, hn, Nat.le_refl _, Nat.le_refl _,
      ⟨hk40, fun _ => ⟨hq8, hqH, hqa, hq48⟩, fun _ => ⟨hqW, hqG⟩⟩,
      ⟨by omega, fun _ => ⟨by omega, held_sub lah (by omega) (by omega),
        M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega), by omega⟩,
        fun _ => ⟨by simp only [AW, Apart] at a1 ⊢; omega, by unfold Apart at a2 ⊢; omega⟩⟩,
      by omega, hxa, hx48, o1, o2, hm.1, hm.2.1, hm.2.2.1, m2, hxN, hnm, hsok, hstw, harr, by omega,
      by omega, o3, by simp only [stUp, Apart] at o4 ⊢; omega, m3, by simp only [stUp, Apart] at m4 ⊢; omega,
      fun _ _ => hqz, fun p c hpc hc0 => ?_, (hga.2.2.2.2 _ (List.mem_cons_self ..)).symm,
      by simp only [stUp, Apart] at hgu ⊢; omega, ⟨CtxB.stnz hB, hga.2.2.1.symm, CtxB.hdr hB⟩, by simp only [stUp, Apart] at hgu ⊢; omega,
      cf_eq hcX (by omega), by unfold xjBud at hbC; omega, hinv⟩
    rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨ox.symm, om.symm, hqS, ?_⟩
      rcases hqB with h | h
      · unfold Apart; omega
      · unfold Apart at h ⊢; omega
    · simp only [stUp, Apart] at o4 m4 hsu
      exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩
  refine divCallG impl hap R nsD stkD costD costF hDiv hnsD hnsW ret hret _ b L g sp K st qp k k
    (stW M st + 8 * (l0 + StackNat.rnd k)) n n xp xl xc mp n mc aDivRet M r18 f29 hRA (by decide) hpre (by omega)
    (by omega) (by omega) (by omega) hxc (by have := hm.2.1; omega) (by omega)
    S4 d1 d2 d3 d4 d5 d6 (by rw [d7, h0]) (by rw [d8, h1]) (by rw [d9, h2]) d10 d11 d12 d13 d14 d15 d16
    (by rw [d17, h18]) (by rw [d18, h28]) (by rw [d19, h29]) (by rw [d20])
    (fun S5 M5 L5 b5 r rl rc e1 e2 e3 e4 e5 e6 e7 e8 e9 hD => ?_)
  have hk5 := keeps_divB hB hKD (List.mem_cons_self ..) hqa hqW hqG hzin (by omega) hD
  have hB5 := CtxB.keep hB hk5
  have hAn5 := Anc.keepB hAn hk5 hl0A
    (by rw [hlen] at hlc; exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hlc) (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexA) hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hcap5 : 0 < stCap M5 st := hk5.2.2.2.2.2.2.2.2.2.2.2.1 hcap
  have hlen5 : stLen M5 st = stLen M st := hD.2.2.2.2.1.1.2.1
  obtain ⟨hxi, hval, hrln, hr64⟩ := rem_xin hrt hsth hsu hsok hcap harr0.1 hzin hn hmV hmB (by omega) hD hcap5
  have hB5' := hB5
  obtain ⟨he5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hl05, -, -, -, -, -, -, -, -, -, -,
    q728, q736, -, -, -, q712, -, q672⟩ := hB5'
  have hb5 : b - costD ≤ b5 := hD.2.2.1
  refine xnA3 impl ret hret _ sp st ylen mp n M5 hal (by omega) hA he5.2.2.2.1 q672 q712 q728 q736 S5 e1 e2 e9
    (fun S6 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 => ?_)
  have hB6 := CtxB.raise (CtxB.dropEx hB5) (l1 := stLen M5 st) (by omega) (Nat.le_refl _)
  refine reaches_mono (xnJStep impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL
    hserv ret hret b5 L5 g sp K n mp mc Mv (Xv % Mv) yp ylen Y yi zp zc st n0 (stLen M5 st) r rl rc rc M5 r18 r29 f29
    hKD hKL hB6 rfl hxi (by rw [hval, hxv]) hrln (by have := hxi.2.2.1; omega) hmB hMo hM1
    (by rw [hlen5, hlen]; omega) (cf_eq hcRB (by omega)) (cf_eq hcRC (by omega)) (by rw [hlen5, hlen]; unfold xjBud at hbC ⊢; omega)
    (by rw [hlen5, hlen]; unfold xjBud at hbB ⊢; omega) hD.2.2.2.1
    L0 bA M0 hAn5 (by rw [hlen5, hlen]; exact ble2 hbAC hb5) (by rw [hlen5, hlen]; exact ble2 hbAB hb5)
    (by rw [hlen5, hlen]; exact Nat.le_trans hl0A (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    S6 g1 g2 g3 (by rw [g4, e3]) (by rw [g5, e4])
    (by rw [g6, e5]) g7 g8 g9 (by rw [g10, e6]) (by rw [g11, e7]) (by rw [g12, e8]) g13)
    (isReturn_mono fun s' h => ?_)
  obtain ⟨l1, zzp, zzc, hl1, h⟩ := h
  exact ⟨l1, zzp, zzc, by omega, h⟩

end FvModexp.Arm64.W2Pro
