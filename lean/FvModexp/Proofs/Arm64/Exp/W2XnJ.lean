import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Xj
import FvModexp.Proofs.Arm64.Exp.W2XnB1
import FvModexp.Proofs.Arm64.Exp.W2XnK

/-!
# window-2 prologue (arm64): path B of the `x` normalisation composed (`xnBK`: `bSnRet` → `RET`)

`XIn`: the facts about the not yet normalised `x = (xp, xl, ·)` at the join `j238` (its array `[xp, xp + 8 xr)` with
`xl ≤ xr`, `0 < xr` — the original `x` or the remainder of `x mod m`); `xjBud`: the budget `xjStep` needs from `xJ` on.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

/-- the `x` operand at the join `j238` -/
@[reducible] def XIn (R : RtInv) (L : List (Nat × Nat)) (sp K st l0 : Nat) (M : Memory) (xp xl xr : Nat) : Prop :=
  xl ≤ xr ∧ 0 < xr ∧ xr < 2 ^ 40 ∧ M.accessible xp (8 * xr) false = true ∧ xp + 8 * xr ≤ 2 ^ 48 ∧
    Obj R L sp K st l0 [] M xp (8 * xr)

/-- the budget of window-2 from `xJ` on (stack level `l`) -/
@[reducible] def xjBud (n costD l : Nat) : Nat :=
  stackNatCost l (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l + StackNat.rnd (2 * n)) (2 * n) +
    (costD + (blockSize (8 * n) true + stackNatCost (l + 2 * StackNat.rnd (2 * n)) (5 * n) +
      blockSize (8 * (2 * n + 4)) true))))

/-- the post of window-2 from the `x` normalisation on (`l1` = the stack level at `xJ`) -/
@[reducible] def XnPost (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g sp n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 : Nat) (r18 r29 : BitVec 64) (s' : State) : Prop :=
  ∃ l1 zzp zzc : Nat, l0 ≤ l1 ∧ l1 + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16 ∧ (2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L0) ∧
    DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv (Exp.newton 64 (Mv % Exp.B)) yp ylen Y yi zp zc st n0
    zzp zzc (l1 + 2 * StackNat.rnd (2 * n)) r18 r29 s'

theorem XIn.keep {R : RtInv} {L L' : List (Nat × Nat)} {g sp K st l0 xp xl xr : Nat} {M M' : Memory}
    (h : XIn R L sp K st l0 M xp xl xr) (hk : KeepsB R L L' g sp K st l0 [] M M') (hl : l0 ≤ stCap M' st) :
    XIn R L' sp K st l0 M' xp xl xr :=
  ⟨h.1, h.2.1, h.2.2.1, by rw [hk.2.1]; exact h.2.2.2.1, h.2.2.2.2.1, objB_keep hk hl h.2.2.2.2.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the memmove/memclr step of path B keeps the context -/
theorem keeps_xb {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {M M' : Memory}
    (hC : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M)
    (hrin : l0 + n ≤ stLen M st)
    (hF : MemFrame M M' (R.rt ++ xbW sp (stW M st + 8 * l0) n))
    (hL : LiveFrame M M' L [(stW M st + 8 * l0, stW M st + 8 * l0 + 8 * n)]) (hrg : M'.regions = M.regions) :
    KeepsB R L L g sp K st l0 [] M M' ∧ stLen M' st = stLen M st ∧ stW M' st = stW M st ∧
      stCap M' st = stCap M st := by
  obtain ⟨-, hce, hK, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hfe, hsth, hstw, hsok, -, hl0, hcap, harr, hug, huw, hsu, -, -, -, -, -,
    -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro'⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  obtain ⟨har1, har2⟩ := harr hcap
  have hstg := hfe.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hfe hLs hd hro'
  simp only [AW, Apart, stUp] at hstw huw hug hsu hga hstg har1 har2
  have ow : ∀ a k, (a + k ≤ sp - K ∨ sp + 752 ≤ a) → (a + k ≤ stW M st + 8 * l0 ∨ stW M st + 8 * l0 + 8 * n ≤ a) →
      Outside a k (xbW sp (stW M st + 8 * l0) n) := by
    intro a k h1 h2; simp only [xbW, outside_cons, outside_nil, and_true]; omega
  have rdh : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → (a + k ≤ sp - K ∨ sp + 752 ≤ a) →
      (a + k ≤ stW M st + 8 * l0 ∨ stW M st + 8 * l0 + 8 * n ≤ a) → M'.readLE a k = M.readLE a k := by
    intro a k hh h1 h2
    rcases hh with hh | hh
    · exact hL.readLE a k hh (by simp only [outside_cons, outside_nil, and_true]; omega)
    · exact hF.readLE a k (by rw [outside_append]; exact ⟨hh, ow a k h1 h2⟩)
  have e0 := rdh st 8 (held_sub hsth (Nat.le_refl _) (by omega)) (by omega) (by omega)
  have e1 := rdh (st + 8) 8 (held_sub hsth (by omega) (by omega)) (by omega) (by omega)
  have e2 := rdh (st + 16) 8 (held_sub hsth (by omega) (by omega)) (by omega) (by omega)
  have hsok' := stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w)
  refine ⟨?_, by simp only [stLen]; rw [e1], by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩
  refine keeps_ofB hce hK (LiveExt.refl R L) hF hL hrg ?_ ?_ ?_ ?_ ?_ ?_ hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _)
    (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
    (arrIn_kept ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
  · clear hstw huw hug hsu hga hstg
    intro r hr hlt
    simp only [xbW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hug hsu hstg
    simp only [xbW, outside_cons, outside_nil, and_true]
    omega
  · clear hstw huw hug hsu hga hstg
    intro a k' ho
    obtain ⟨-, o2, -, o4, -⟩ := ho
    simp only [AW, Apart, stUp] at o2 o4
    refine ⟨ow _ _ (by omega) (by omega), ?_⟩
    simp only [outside_cons, outside_nil, and_true]
    omega
  all_goals clear hstw huw hug hsu hga hstg
  all_goals simp only [xbW, outside_cons, outside_nil, and_true]
  · intro j hj; omega
  · omega
  · omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path B from the return of `rr := stk.nat(n)` (`bSnRet`) to the function's `RET` -/
theorem xnBK (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xr : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M)
    (hlen : stLen M st = l0 + StackNat.rnd n)
    (hx : XIn R L sp K st l0 M xp xl xr) (hxv : M.readLE xp (8 * xl) = Xv) (hxl : xl < n)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcF : costF (l0 + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (r312 : M.readLE (sp + 312) 8 = xl) (r608 : M.readLE (sp + 608) 8 = xp)
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbA : bA + xjBudA n costD (l0 + StackNat.rnd n) ≤ b) (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 bSnRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 (stW M st + 8 * l0)) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h2 : S.regs 2 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (XnPost R L0 K bA M0 g sp n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 r18 r29)) := by
  have hB0 := hB
  obtain ⟨he, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsok, -, -, hcap, harr, -, -, hsu, -, -, -, -, -,
    r728, r736, -, -, -, r712, -, r672⟩ := hB0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, hga, -, -, -, -⟩ := hce0
  have hsok0 := hsok
  obtain ⟨-, -, -, -, hlive, hlc, -⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  obtain ⟨har1, har2⟩ := harr hcap
  obtain ⟨hxl', hxr0, hxr40, hxa, hx48, ⟨o1, o2, o3, o4, -⟩⟩ := hx
  have hrn : n ≤ StackNat.rnd n := by simp only [StackNat.rnd]; omega
  have hrin : l0 + n ≤ stLen M st := by omega
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  have hclrL := MemclrNoHeapPointersLive.of_codeIn hc hclr
  have u1 := har1; have u2 := har2; have u3 := o2; have u4 := o4
  simp only [AW, Apart, stUp] at u1 u2 u3 u4
  refine xnB impl R hmvL hclrL ret hret _ L g sp n xp xl (stW M st + 8 * l0) st ylen mp M he hn128 hxl
    (M.accessible_sub hxa (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega) (held_sub o1 (Nat.le_refl _) (by omega))
    (by unfold Apart; omega) (M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)) (by omega)
    (held_sub lah (by omega) (by omega)) (by unfold Apart; omega) (by unfold Apart; omega) (by omega)
    (by unfold Apart; omega) (hserv.2.1 _ _ _ (by omega)) (hserv.2.2.1 _ _ (by omega)) b hinv r736 r312 r608
    S hpc hsp h0 h1 h2 r672 r712 r728 r18 f29 h18 h29 h28 hmem
    (fun S3 M3 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 hF hL hI hrg hv => ?_)
  obtain ⟨hk, hlen3, hW3, hcap3⟩ := keeps_xb hB hrin hF hL hrg
  have hB3 := CtxB.keep hB hk
  have hAn3 := Anc.keepB hAn hk hl0A (le_cap_of hlen hlc) (fun e he => by simp at he) hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hB4 := CtxB.raise hB3 (l1 := l0 + StackNat.rnd n) (by omega) (by omega)
  have hx3 : Inp R L sp n M3 (stW M st + 8 * l0) :=
    ⟨by rw [hF.accessible]; exact M.accessible_sub laacc (Or.inl rfl) (by omega) (by omega), by omega,
      held_sub lah (by omega) (by omega), by unfold Apart; omega⟩
  have hxO3 : Obj R L sp K st (l0 + StackNat.rnd n) [] M3 (stW M st + 8 * l0) (8 * n) := by
    refine ⟨held_sub lah (by omega) (by omega), by simp only [AW, Apart]; omega, ?_, ?_, fun e he => by simp at he⟩
    · have := hsu; simp only [Apart, stUp] at this ⊢; omega
    · simp only [stUp, Apart]; rw [hW3, hcap3]; omega
  refine reaches_mono (xjStep impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL hserv
    ret hret b L g sp K n mp mc Mv (stW M st + 8 * l0) n Xv yp ylen Y yi zp zc st n0 (l0 + StackNat.rnd n) M3 r18 r29 f29
    hKD hKL hB4 (by rw [hlen3, hlen]) hx3 hxO3 (by rw [hv, hxv]) (by omega) hmB hMo hM1 (by omega) (cf_eq hcF (by omega)) hbud hI
    L0 bA M0 hAn3 hbA (Nat.le_trans hl0A (Nat.le_add_right _ _))
    S3 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13) (isReturn_mono fun s' h => ?_)
  obtain ⟨zzp, zzc, hfr, h⟩ := h
  exact ⟨l0 + StackNat.rnd n, zzp, zzc, Nat.le_add_right _ _, hslen, hfr, h⟩

theorem obj_sub {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 a k b k' : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : Obj R L sp K st l0 ex M a k) (h1 : a ≤ b) (h2 : b + k' ≤ a + k) : Obj R L sp K st l0 ex M b k' := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := h
  refine ⟨held_sub o1 h1 h2, by simp only [AW, Apart] at o2 ⊢; omega, by unfold Apart at o3 ⊢; omega,
    by simp only [Apart] at o4 ⊢; omega, fun e he => by have := o5 e he; unfold Apart at this ⊢; omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `x` join `j238` (`len x ≤ n`) to the function's `RET`: path C (`len x = n`, nothing to do) or path B
(`rr := stk.nat(n)`, copy, clear) -/
theorem xnJStep (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xr xc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M) (hl0e : stLen M st = l0)
    (hx : XIn R L sp K st l0 M xp xl xr) (hxv : M.readLE xp (8 * xl) = Xv) (hxln : xl ≤ n) (hxc : xc < 2 ^ 64)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcF : costF (l0 + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hcFC : costF (l0 + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbC : xjBud n costD l0 ≤ b) (hbB : stackNatCost l0 n + xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbAC : bA + xjBudA n costD l0 ≤ b) (hbAB : bA + (stackNatCost l0 n + xjBudA n costD (l0 + StackNat.rnd n)) ≤ b)
    (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 j238) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h8 : S.regs 8 = BitVec.ofNat 64 ylen) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (XnPost R L0 K bA M0 g sp n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 r18 r29)) := by
  have hB0 := hB
  obtain ⟨he, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, hcap, harr, -, huw, hsu, hgl, -, hstwb, -, -,
    -, -, -, -, -, -, -, -⟩ := hB0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hx0 := hx
  obtain ⟨hxl', hxr0, hxr40, hxa, hx48, hxO⟩ := hx0
  have hst48 := hsok.2.2.2.1
  refine xnJ impl ret hret _ sp st xp xl n M hal (by omega) hA (M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega))
    (by omega) (by omega) (by omega) hn128 S hpc hsp h3 h4 h5 h11 hmem ?_ ?_
  · -- path C: `len x = n`
    intro hc S' c1 c2 c3 c4
    have hxn : xl = n := by omega
    subst hxn
    have hxO' := hxO
    obtain ⟨o1, o2, -, -, -⟩ := hxO'
    simp only [AW, Apart] at o2
    refine reaches_mono (xjStep impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL
      hserv ret hret b L g sp K xl mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 M r18 r29 f29 hKD hKL hB hl0e
      ⟨M.accessible_sub hxa (Or.inl rfl) (Nat.le_refl _) (by omega), by omega, held_sub o1 (Nat.le_refl _) (by omega),
        by unfold Apart; omega⟩
      (obj_sub hxO (Nat.le_refl _) (by omega)) hxv hxc hmB hMo hM1 (by omega) (cf_eq hcFC (by omega)) hbC hinv L0 bA M0 hAn hbAC hl0A S' c1 (by rw [c2, hsp])
      (by rw [c4, h3]) (by rw [c4, h4]) (by rw [c4, h5]) (by rw [c4, h6]) (by rw [c4, h8]) (by rw [c4, h10])
      (by rw [c4, h11]) (by rw [c4, h18]) (by rw [c4, h28]) (by rw [c4, h29]) (by rw [c3, hmem]))
      (isReturn_mono fun s' h => ?_)
    obtain ⟨zzp, zzc, hfr, h⟩ := h
    exact ⟨l0, zzp, zzc, Nat.le_refl _, le_drop hslen, hfr, h⟩
  · -- path B: `len x < n`
    intro hc S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 cm hmf hrg q312 q608
    have ws_in : ∀ r ∈ [(sp + 312, sp + 320), (sp + 608, sp + 616)], sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 752 := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (simp only; omega)
    have hk1 := keeps_ownB hB hmf hrg ws_in (fun j hj => by simp only [outside_cons, outside_nil, and_true]; omega)
    have hB1 := CtxB.keep hB hk1
    have hAn1 := Anc.keepB hAn hk1 hl0A (by rw [← hl0e]; exact hsok.2.2.2.2.2.1) (fun e he => by simp at he)
      hce.2.2.2.2.2.2.2.2.2.2.1 hK0
    have hlen1 : stLen M1 st = l0 := by
      rw [← hl0e]; exact hmf.readLE _ _ (by
        have := hstw; simp only [AW, Apart] at this; simp only [outside_cons, outside_nil, and_true]; omega)
    have hl01 : l0 ≤ stCap M1 st := by rw [← hlen1]; exact hk1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
    have hx1 := XIn.keep hx hk1 hl01
    have hxv1 : M1.readLE xp (8 * xl) = Xv := by
      rw [hk1.2.2.2.1 _ _ (obj_sub hxO (Nat.le_refl _) (by omega))]; exact hxv
    have hinv1 : R.inv b L g (view R.rt L M1) := by
      refine FvModexp.Expmc.inv_frame hmf (fun r hr => Or.inr ?_) hinv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hrt.of_sub (by omega) (by omega)
    have hB1' := hB1
    obtain ⟨-, hce1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, hstw1, hsok1, -, -, hcap1, harr1, -, huw1, hsu1, hgl1, -, hstwb1, -, -,
      -, -, -, -, -, -, -, -⟩ := hB1'
    have hrn : n ≤ StackNat.rnd n := by simp only [StackNat.rnd]; omega
    have hpre : SnPre R b L g sp st n M1 := by
      refine ⟨CallW.CEnv.mono hce1 hK (Nat.le_refl _), hserv, hsok1,
        Apart.sub hstw1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega),
        fun hc => ⟨Apart.sub (harr1 hc).1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega), (harr1 hc).2⟩,
        by omega, by rw [hlen1]; omega, by rw [hlen1]; unfold xjBud at hbB; omega, hinv1, hgl1.2.2.2.2.2.2.2.2.2.2.1,
        hstwb1, (in_stUp hsu1 (by simp only [stFree]; rw [hlen1]; omega) (by simp only [stFree]; omega))⟩
    have hRA : RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) bSnRet :=
      CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := StackNat.names)
        (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 149
        (by decide) (by decide) (by decide)
    refine snCallK impl hap R hSN ret hret _ b L g sp n st bSnRet M1 r18 f29 hRA (by decide) hpre (by omega)
      (by omega) S1 c1 c2 c3 c4 c5 (by rw [c6, h18]) (by rw [c7, h28]) (by rw [c8, h29]) cm
      (fun S2 M2 L2 b2 f1 f2 f3 f4 f5 f6 f7 f8 f9 hS => ?_)
    have hk2 := keeps_snB hB1 hn hS
    have hB2 := CtxB.keep hB1 hk2
    have hAn2 := Anc.keepB hAn1 hk2 hl0A hl01 (fun e he => by simp at he) hce1.2.2.2.2.2.2.2.2.2.2.1 hK0
    have hS0 := hS
    obtain ⟨hx2, hb2, hinv2, hsok2, hlen2, -, -, -, -, -⟩ := hS0
    rw [hlen1] at f3 hlen2 hb2
    have hl02 : l0 ≤ stCap M2 st := by have := hsok2.2.2.2.2.2.1; omega
    have hxI2 := XIn.keep hx1 hk2 hl02
    have hxv2 : M2.readLE xp (8 * xl) = Xv := by
      rw [hk2.2.2.2.1 _ _ (obj_sub hx1.2.2.2.2.2 (Nat.le_refl _) (by omega))]; exact hxv1
    have hrt4 : Outside (sp - 4304) (4304 + 752) R.rt := hrt.of_sub (by omega) (by omega)
    have hfw : Apart (stFree M1 st).1 (stFree M1 st).2 (sp - 4304) (4304 + 752) :=
      Apart.sub (in_stUp huw1.symm (by simp only [stFree]; rw [hlen1]; omega) (by simp only [stFree]; omega)).symm
        (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
    have sl : ∀ j, 24 ≤ j → j + 8 ≤ 752 → M2.readLE (sp + j) 8 = M1.readLE (sp + j) 8 := fun j a b =>
      slot_sn hS hrt4 (by omega) (Apart.sub hstw1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)) hfw j a b
    refine reaches_mono (xnBK impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL hserv
      ret hret b2 L2 g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xr M2 r18 r29 f29 hKD hKL hB2 hlen2 hxI2 hxv2
      (by omega) hmB hMo hM1 hslen hcF (by omega) hinv2
      (by rw [sl 312 (by omega) (by omega)]; exact q312) (by rw [sl 608 (by omega) (by omega)]; exact q608)
      L0 bA M0 hAn2 (ble2 hbAB hb2) hl0A
      S2 f1 f2 f3 f4 f5 f6 f7 f8 f9) (isReturn_mono fun s' h => ?_)
    obtain ⟨l1, zzp, zzc, hl1, h⟩ := h
    exact ⟨l1, zzp, zzc, by omega, h⟩

end FvModexp.Arm64.W2Pro
