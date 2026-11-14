import FvModexp.Proofs.Arm64.Exp.W2XnDefs
import FvModexp.Proofs.Arm64.Exp.W2FunDefs
import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2XnA

/-!
# window-2 prologue (arm64): the whole `x` normalisation (nat.go:1377-1386) from `xnE` (fn+0x1a4) to the function's `RET`

`xnAStep`: path A (`len x > n`: `q := stk.nat(len x - n + 1)`, `z2 := stk.nat(n)`, then `xnA2K`);
`xnStep`: the split at `xnE` (path A, or the join `j238` with the original `x`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

/-- budget step for `xnAStep` (small context; omega in the step's context cost 15 s each) -/
theorem bud3 {b b2 b4 x y z : Nat} (h : x + (y + z) ≤ b) (h2 : b - x ≤ b2) (h4 : b2 - y ≤ b4) : z ≤ b4 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnAStep (hRR : FvModexp.Arm64.W2Pro.RRSpec) (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) {lu : Nat} (hlu : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n ≤ lu) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M) (hl0e : stLen M st = l0)
    (hxO : Obj R L sp K st l0 [] M xp (8 * xl)) (hxa : M.accessible xp (8 * xl) false = true)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxN : NatNorm M xp xl) (hxl : n < xl) (hxl' : xl ≤ 128) (hxc : xc < 2 ^ 64)
    (hxv : M.readLE xp (8 * xl) = Xv)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n + 2 * StackNat.rnd (2 * n) +
      32 * n + 80 ≤ 2 ^ 16)
    (hcs : DivCosts costF costD n xl l0)
    (hbA : xnBudA n costD l0 (xl - n + 1) ≤ b) (hbAC : xnBudAC n costD l0 (xl - n + 1) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (r680 : M.readLE (sp + 680) 8 = xp) (r688 : M.readLE (sp + 688) 8 = xl) (r696 : M.readLE (sp + 696) 8 = xc)
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbAB : bA + xnBudAB n costD l0 (xl - n + 1) ≤ b) (hbAA : bA + xnBudAA n costD l0 (xl - n + 1) ≤ b)
    (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 snE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 (xl - n + 1))
    (h30 : S.regs 30 = BitVec.ofNat 64 aSn1Ret)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (XnPost R L0 K bA M0 g sp n mp mc Mv (Xv % Mv) yp ylen Y yi zp zc st n0 l0 lu r18 r29)) := by
  have hB0 := hB
  obtain ⟨he, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, hcap, harr, -, huw, hsu, hgl, -, hstwb, -, -,
    -, -, -, -, -, -, -, -⟩ := hB0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hst48 := hsok.2.2.2.1
  obtain ⟨k, hkdef⟩ : ∃ k, k = xl - n + 1 := ⟨_, rfl⟩
  rw [← hkdef] at hslen hbA hbAC h1 hbAB hbAA
  have hk0 : 0 < k := by omega
  have hrk : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega
  have hrn : n ≤ StackNat.rnd n := by simp only [StackNat.rnd]; omega
  -- `q := stk.nat(k)`
  have hpre1 : SnPre R b L g sp st k M := by
    refine ⟨CallW.CEnv.mono hce hK (Nat.le_refl _), hserv, hsok,
      Apart.sub hstw (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega),
      fun hc => ⟨Apart.sub (harr hc).1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega), (harr hc).2⟩,
      by omega, by rw [hl0e]; omega, by rw [hl0e]; unfold xnBudA at hbA; omega, hinv, hgl.2.2.2.2.2.2.2.2.2.2.1,
      hstwb, (in_stUp hsu (by simp only [stFree]; rw [hl0e]; omega) (by simp only [stFree]; omega))⟩
  have hRA1 : RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) aSn1Ret :=
    CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := StackNat.names)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 111
      (by decide) (by decide) (by decide)
  refine snCallK impl hap R hSN ret hret _ b L g sp k st aSn1Ret M r18 f29 hRA1 (by decide) hpre1 (by omega)
    hk0 S hpc hsp h0 h1 h30 h18 h28 h29 hmem (fun S2 M2 L2 b2 f1 f2 f3 f4 f5 f6 f7 f8 f9 hS1 => ?_)
  have hk2 := keeps_snB hB hk0 hS1
  have hB2 := CtxB.keep hB hk2
  have hAn2 := Anc.keepB hAn hk2 hl0A (by rw [← hl0e]; exact hsok.2.2.2.2.2.1) (fun e he => by simp at he)
    hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hS10 := hS1
  obtain ⟨hx2, hb2, hinv2, hsok2, hlen2, -, -, -, -, -⟩ := hS10
  rw [hl0e] at f3 hlen2 hb2
  have hlc2 := hsok2.2.2.2.2.2.1
  have hcap2 : 0 < stCap M2 st := hk2.2.2.2.2.2.2.2.2.2.2.2.1 hcap
  obtain ⟨q8, qH, qacc, q48⟩ := hsok2.2.2.2.2.1 hcap2
  have hqin : stW M2 st + 8 * l0 ≤ (stW M2 st + 8 * l0, 8 * k).1 ∧
      (stW M2 st + 8 * l0, 8 * k).1 + (stW M2 st + 8 * l0, 8 * k).2 ≤ stW M2 st + 8 * stCap M2 st := by
    simp only; omega
  have hB2' := CtxB.addEx hB2 hqin
  have hB2a := hB2
  obtain ⟨-, hce2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw2, -, -, -, -, harr2, -, huw2, hsu2, -, -, -, -, -,
    -, r736, -, -, -, -, -, r672⟩ := hB2a
  obtain ⟨a1, a2⟩ := harr2 hcap2
  have hl02 : l0 ≤ stCap M2 st := by omega
  have hxO2 : Obj R L2 sp K st l0 [(stW M2 st + 8 * l0, 8 * k)] M2 xp (8 * xl) :=
    obj_addEx (objB_keep hk2 hl02 hxO) hqin
  -- the spills of `q`
  refine xnA1 impl ret hret _ sp st n (stW M2 st + 8 * l0) k k M2 hal (by omega) hA
    (by rw [hk2.2.1]; exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) (by omega) (by omega) (by omega)
    r672 r736 S2 f1 f2 f3 f4 f5 f9 (fun S3 M3 c1 c2 c3 c4 c5 c6 c7 c8 cm hmf hrg q616 q328 q320 => ?_)
  have ws_in : ∀ r ∈ [(sp + 320, sp + 336), (sp + 616, sp + 624)], sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 752 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only; omega)
  have hk3 := keeps_ownB hB2' hmf hrg ws_in (fun j hj => by simp only [outside_cons, outside_nil, and_true]; omega)
  have hB3 := CtxB.keep hB2' hk3
  have hexq : ALoc R L0 st M0 (stW M2 st + 8 * l0, 8 * k) := aloc_of_anc hAn2 hl0A (by have := hqin.2; simp only at this; exact cap_of_in this)
  have hAn3 := Anc.keepB hAn2 hk3 hl0A hl02 (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexq) hce2.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hst2 : Apart st 24 (sp - K) (K + 752) := hstw2
  have e0 : M3.readLE st 8 = M2.readLE st 8 := hmf.readLE _ _ (by
    simp only [AW, Apart] at hst2; simp only [outside_cons, outside_nil, and_true]; omega)
  have e1 : M3.readLE (st + 8) 8 = M2.readLE (st + 8) 8 := hmf.readLE _ _ (by
    simp only [AW, Apart] at hst2; simp only [outside_cons, outside_nil, and_true]; omega)
  have hW3 : stW M3 st = stW M2 st := by simp only [stW]; rw [e0]
  have hlen3 : stLen M3 st = l0 + StackNat.rnd k := by simp only [stLen] at hlen2 ⊢; rw [e1]; exact hlen2
  have hinv3 : R.inv b2 L2 g (view R.rt L2 M3) := by
    refine FvModexp.Expmc.inv_frame hmf (fun r hr => Or.inr ?_) hinv2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hrt.of_sub (by omega) (by omega)
  -- `z2 := stk.nat(n)`
  have hB3a := hB3
  obtain ⟨-, hce3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw3, hsok3, -, -, hcap3, harr3, -, huw3, hsu3, hgl3, -, hstwb3, -, -,
    -, -, -, -, -, -, -, -⟩ := hB3a
  have hpre2 : SnPre R b2 L2 g sp st n M3 := by
    refine ⟨CallW.CEnv.mono hce3 hK (Nat.le_refl _), hserv, hsok3,
      Apart.sub hstw3 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega),
      fun hc => ⟨Apart.sub (harr3 hc).1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega), (harr3 hc).2⟩,
      by omega, by rw [hlen3]; omega, by rw [hlen3]; unfold xnBudA at hbA; omega, hinv3, hgl3.2.2.2.2.2.2.2.2.2.2.1,
      hstwb3, (in_stUp hsu3 (by simp only [stFree]; rw [hlen3]; omega) (by simp only [stFree]; omega))⟩
  have hRA2 : RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) aSn2Ret :=
    CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := StackNat.names)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 117
      (by decide) (by decide) (by decide)
  refine snCallK impl hap R hSN ret hret _ b2 L2 g sp n st aSn2Ret M3 r18 f29 hRA2 (by decide) hpre2 (by omega)
    hn S3 c1 c2 c3 c4 c5 (by rw [c6, f6]) (by rw [c7, f7]) (by rw [c8, f8]) cm
    (fun S4 M4 L4 b4 g1 g2 g3 g4 g5 g6 g7 g8 g9 hS2 => ?_)
  have hk4 := keeps_snB hB3 hn hS2
  have hB4 := CtxB.keep hB3 hk4
  have hAn4 := Anc.keepB hAn3 hk4 hl0A (le_cap_of hlen3 hsok3.2.2.2.2.2.1) (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexq) hce3.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hS20 := hS2
  obtain ⟨hx4, hb4, hinv4, hsok4, hlen4, -, -, -, -, -⟩ := hS20
  rw [hlen3] at g3 hlen4 hb4
  have hqH3 : Held R L2 (stW M2 st + 8 * l0) (8 * k) := held_sub qH (by omega) (by omega)
  obtain ⟨hqB, hqz⟩ := below_sn (l0 := l0) hS2 hqH3 (Or.inl ⟨by rw [hW3]; exact Nat.le_refl _, by rw [hW3, hlen3]; omega⟩)
  rw [hlen3] at hqz
  have hrt4 : Outside (sp - 4304) (4304 + 752) R.rt := hrt.of_sub (by omega) (by omega)
  have hfw : Apart (stFree M3 st).1 (stFree M3 st).2 (sp - 4304) (4304 + 752) :=
    Apart.sub (in_stUp huw3.symm (by simp only [stFree]; rw [hlen3]; omega) (by simp only [stFree]; omega)).symm
      (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
  have sl : ∀ j, 24 ≤ j → j + 8 ≤ 752 → M4.readLE (sp + j) 8 = M3.readLE (sp + j) 8 := fun j a b =>
    slot_sn hS2 hrt4 (by omega) (Apart.sub hstw3 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)) hfw j a b
  have rk : ∀ j, 624 ≤ j → j + 8 ≤ 752 → M4.readLE (sp + j) 8 = M.readLE (sp + j) 8 := fun j a b => by
    rw [hk4.2.2.2.2.1 j (by omega), hk3.2.2.2.2.1 j (by omega), hk2.2.2.2.2.1 j (by omega)]
  have hl04 : l0 ≤ stCap M4 st := by have := hsok4.2.2.2.2.2.1; omega
  have hl03 : l0 ≤ stCap M3 st := by have := hsok3.2.2.2.2.2.1; omega
  have hxO3 := objB_keep hk3 hl03 hxO2
  have hxO4 := objB_keep hk4 hl04 hxO3
  have rdx : ∀ a c, xp ≤ a → a + c ≤ xp + 8 * xl → M4.readLE a c = M.readLE a c := fun a c h1 h2 => by
    rw [hk4.2.2.2.1 _ _ (obj_sub hxO3 h1 h2), hk3.2.2.2.1 _ _ (obj_sub hxO2 h1 h2),
      hk2.2.2.2.1 _ _ (obj_sub hxO h1 h2)]
  have hxN4 : NatNorm M4 xp xl := by
    rcases hxN with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [rdx _ _ (by omega) (by omega)]; exact h)
  refine reaches_mono (xnA2K (hRR := hRR) (lu := lu) (hlu := by rw [hkdef]; exact hlu) impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL
    hserv ret hret b4 L4 g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xc (stW M2 st + 8 * l0) k M4 r18 r29 f29
    hKD hKL hB4 (by rw [hlen4]) hk0 (by omega) (by omega) (hx4.held hqH3)
    (by rw [hk4.2.1, hk3.2.1]; exact M2.accessible_sub qacc (Or.inr rfl) (by omega) (by omega)) (by omega)
    (Apart.sub a1 (Nat.le_add_right _ _) hqin.2 (Nat.le_refl _) (Nat.le_refl _))
    (Apart.sub a2 (Nat.le_add_right _ _) hqin.2 (Nat.le_refl _) (Nat.le_refl _))
    (by have := hsu2; simp only [stUp, Apart] at this ⊢; omega) hqB hqz hxO4
    (by rw [hk4.2.1, hk3.2.1, hk2.2.1]; exact hxa) hx48 hxN4 hxl hxl' hxc
    (by rw [rdx _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hxv) hmB hMo hM1 (by omega) (by rw [hkdef]; exact hcs.1) (by rw [hkdef]; exact hcs.2.1) (by rw [hkdef]; exact hcs.2.2.1)
    (bud3 hbAC hb2 hb4) (bud3 hbA hb2 hb4) hinv4
    (by rw [sl 616 (by omega) (by omega)]; exact q616) (by rw [sl 328 (by omega) (by omega)]; exact q328)
    (by rw [sl 320 (by omega) (by omega)]; exact q320) (by rw [rk 680 (by omega) (by omega)]; exact r680)
    (by rw [rk 688 (by omega) (by omega)]; exact r688) (by rw [rk 696 (by omega) (by omega)]; exact r696)
    L0 bA M0 hAn4 (ble3 hbAA hb2 hb4) (ble3 hbAB hb2 hb4) hl0A hexq
    S4 g1 g2 g3 g4 g5 g6 g7 g8 g9) (isReturn_mono fun s' h => h)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the whole `x` normalisation from `xnE` (fn+0x1a4) to the function's `RET`; the normalised `x` is `≡ x (mod m)` -/
theorem xnStep (hRR : FvModexp.Arm64.W2Pro.RRSpec) (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) {lu : Nat} (hlu : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n ≤ lu) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M) (hl0e : stLen M st = l0)
    (hxO : Obj R L sp K st l0 [] M xp (8 * xl)) (hxa : M.accessible xp (8 * xl) false = true)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxN : NatNorm M xp xl) (hxl0 : 0 < xl) (hxl' : xl ≤ 128) (hxc : xc < 2 ^ 64)
    (hxv : M.readLE xp (8 * xl) = Xv)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n + 2 * StackNat.rnd (2 * n) +
      32 * n + 80 ≤ 2 ^ 16)
    (hcs : DivCosts costF costD n xl l0)
    (hbC : xjBud n costD l0 ≤ b) (hbB : stackNatCost l0 n + xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hbA : xnBudA n costD l0 (xl - n + 1) ≤ b) (hbAC : xnBudAC n costD l0 (xl - n + 1) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (r680 : M.readLE (sp + 680) 8 = xp) (r688 : M.readLE (sp + 688) 8 = xl) (r696 : M.readLE (sp + 696) 8 = xc)
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbAC' : bA + xjBudA n costD l0 ≤ b) (hbAB' : bA + (stackNatCost l0 n + xjBudA n costD (l0 + StackNat.rnd n)) ≤ b)
    (hbAAB : bA + xnBudAB n costD l0 (xl - n + 1) ≤ b) (hbAAA : bA + xnBudAA n costD l0 (xl - n + 1) ≤ b)
    (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xnE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h8 : S.regs 8 = BitVec.ofNat 64 ylen) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ Xv', Xv' % Mv = Xv % Mv ∧ Xv' < Exp.B ^ n ∧
        XnPost R L0 K bA M0 g sp n mp mc Mv Xv' yp ylen Y yi zp zc st n0 l0 lu r18 r29 s')) := by
  have hst64 : st < 2 ^ 64 := by have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1; omega
  have hn128 : n ≤ 128 := hB.2.2.2.2.2.1
  refine xnSplit impl ret hret _ st xl n hst64 (by omega) hn128 S hpc h3 h5 h11 ?_ ?_
  · intro hc S' c1 c2 c3 c4
    have hxO' := hxO
    obtain ⟨-, o2, -, -, -⟩ := hxO'
    refine reaches_mono (xnJStep (hRR := hRR) (lu := lu) (hlu := by omega) impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL
      hserv ret hret b L g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xl xc M r18 r29 f29 hKD hKL hB hl0e
      ⟨Nat.le_refl _, hxl0, by omega, hxa, hx48, hxO⟩ hxv hc hxc hmB hMo hM1 (by omega) hcs.2.2.2.1 hcs.2.2.2.2 hbC hbB hinv
      L0 bA M0 hAn hbAC' hbAB' hl0A S' c1
      (by rw [c2, hsp]) (by rw [c4, h3]) (by rw [c4, h4]) (by rw [c4, h5]) (by rw [c4, h6]) (by rw [c4, h8])
      (by rw [c4, h10]) (by rw [c4, h11]) (by rw [c4, h18]) (by rw [c4, h28]) (by rw [c4, h29]) (by rw [c3, hmem]))
      (isReturn_mono fun s' h => ⟨Xv, rfl, by
        rw [← hxv]; exact Nat.lt_of_lt_of_le (FvModexp.Expmc.readLE_lt_B _ _ _) (Nat.pow_le_pow_right Exp.B_pos hc), h⟩)
  · intro hc S' c1 c2 c3 c4 c5 c6 c7 c8 c9
    refine reaches_mono (xnAStep (hRR := hRR) (lu := lu) (hlu := hlu) impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL
      hserv ret hret b L g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xc M r18 r29 f29 hKD hKL hB hl0e hxO hxa
      hx48 hxN hc hxl' hxc hxv hmB hMo hM1 hslen hcs hbA hbAC hinv r680 r688 r696 L0 bA M0 hAn hbAAB hbAAA hl0A S' c1 (by rw [c2, hsp]) c4 c5 c6
      (by rw [c7, h18]) (by rw [c8, h28]) (by rw [c9, h29]) (by rw [c3, hmem]))
      (isReturn_mono fun s' h => ⟨Xv % Mv, Nat.mod_mod _ _, Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hM1)) hmB, h⟩)

end FvModexp.Arm64.W2Pro
