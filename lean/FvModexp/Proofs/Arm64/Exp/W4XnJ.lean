import FvModexp.Proofs.Arm64.Exp.W4XnB1
import FvModexp.Proofs.Arm64.Exp.W4XnK

/-!
# window-4 prologue (arm64): path B of the `x` normalisation composed (`xnBK`: `bSnRet` → `RET`)

`XIn`: the facts about the not yet normalised `x = (xp, xl, ·)` at the join `j238` (its array `[xp, xp + 8 xr)` with
`xl ≤ xr`, `0 < xr` — the original `x` or the remainder of `x mod m`); `xjBud`: the budget `xjStep` needs from `xJ` on.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

/-- the `x` operand at the join `j238` -/
@[reducible] def XIn (R : RtInv) (L : List (Nat × Nat)) (sp K st l0 : Nat) (M : Memory) (xp xl xr : Nat) : Prop :=
  xl ≤ xr ∧ 0 < xr ∧ xr < 2 ^ 40 ∧ M.accessible xp (8 * xr) false = true ∧ xp + 8 * xr ≤ 2 ^ 48 ∧
    Obj R L sp K st l0 [] M xp (8 * xr)

/-- the budget of window-4 from `xJ` on (stack level `l`) -/
@[reducible] def xjBud (n costD l : Nat) : Nat :=
  stackNatCost l (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l + StackNat.rnd (2 * n)) (2 * n) +
    (costD + (blockSize (8 * n) true + stackNatCost (l + 2 * StackNat.rnd (2 * n)) (17 * n) +
      blockSize (8 * (2 * n + 4)) true))))

/-- the post of window-4 from the `x` normalisation on (`l1` = the stack level at `xJ`) -/
@[reducible] def XnPost (R : RtInv) (g sp n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 : Nat) (r18 r29 : BitVec 64)
    (s' : State) : Prop :=
  ∃ l1 zzp zzc : Nat, l0 ≤ l1 ∧ DivRetPost R g sp n mp mc Mv Xv (Exp.newton 64 (Mv % Exp.B)) yp ylen Y yi zp zc st n0
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
  have ow : ∀ a k, (a + k ≤ sp - K ∨ sp + 1040 ≤ a) → (a + k ≤ stW M st + 8 * l0 ∨ stW M st + 8 * l0 + 8 * n ≤ a) →
      Outside a k (xbW sp (stW M st + 8 * l0) n) := by
    intro a k h1 h2; simp only [xbW, outside_cons, outside_nil, and_true]; omega
  have rdh : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → (a + k ≤ sp - K ∨ sp + 1040 ≤ a) →
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
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costD)
    (hnsD : ∀ x, nsD.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : ExpHyp.LshHyp impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibExp.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg34.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xr : Nat)
    (M : Memory) (r18 r29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M)
    (hlen : stLen M st = l0 + StackNat.rnd n)
    (hx : XIn R L sp K st l0 M xp xl xr) (hxv : M.readLE xp (8 * xl) = Xv) (hxl : xl < n)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 17 * n + 68 ≤ 2 ^ 16)
    (hbud : xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (r312 : M.readLE (sp + 312) 8 = xl) (r896 : M.readLE (sp + 896) 8 = xp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 bSnRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 (stW M st + 8 * l0)) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h2 : S.regs 2 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M) :
    Reaches ((LibExp.program.link impl).withExit ret) S
      (IsReturn (XnPost R g sp n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 r18 r29)) := by
  have hB0 := hB
  obtain ⟨he, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsok, -, -, hcap, harr, -, -, hsu, -, -, -, -, -,
    r1016, r1024, -, -, -, r1000, -, r960⟩ := hB0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, hga, -, -, -, -⟩ := hce0
  have hsok0 := hsok
  obtain ⟨-, -, -, -, hlive, hlc, -⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  obtain ⟨har1, har2⟩ := harr hcap
  obtain ⟨hxl', hxr0, hxr40, hxa, hx48, ⟨o1, o2, o3, o4, -⟩⟩ := hx
  have hrn : n ≤ StackNat.rnd n := by simp only [StackNat.rnd]; omega
  have hrin : l0 + n ≤ stLen M st := by omega
  have hc := codeIn_ofImpl_restrict_of_apart hap LibExp.names
  rw [← LibExp.eq_only] at hc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  have hclrL := MemclrNoHeapPointersLive.of_codeIn hc hclr
  have u1 := har1; have u2 := har2; have u3 := o2; have u4 := o4
  simp only [AW, Apart, stUp] at u1 u2 u3 u4
  refine xnB impl R hmvL hclrL ret hret _ L g sp n xp xl (stW M st + 8 * l0) st ylen mp M he hn128 hxl
    (M.accessible_sub hxa (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega) (held_sub o1 (Nat.le_refl _) (by omega))
    (by unfold Apart; omega) (M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)) (by omega)
    (held_sub lah (by omega) (by omega)) (by unfold Apart; omega) (by unfold Apart; omega) (by omega)
    (by unfold Apart; omega) (hserv.2.1 _ _ _ (by omega)) (hserv.2.2.1 _ _ (by omega)) b hinv r1024 r312 r896
    S hpc hsp h0 h1 h2 r960 r1000 r1016 r18 r29 h18 h29 h28 hmem
    (fun S3 M3 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 hF hL hI hrg hv => ?_)
  obtain ⟨hk, hlen3, hW3, hcap3⟩ := keeps_xb hB hrin hF hL hrg
  have hB3 := CtxB.keep hB hk
  have hB4 := CtxB.raise hB3 (l1 := l0 + StackNat.rnd n) (by omega) (by omega)
  have hx3 : Inp R L sp n M3 (stW M st + 8 * l0) :=
    ⟨by rw [hF.accessible]; exact M.accessible_sub laacc (Or.inl rfl) (by omega) (by omega), by omega,
      held_sub lah (by omega) (by omega), by unfold Apart; omega⟩
  have hxO3 : Obj R L sp K st (l0 + StackNat.rnd n) [] M3 (stW M st + 8 * l0) (8 * n) := by
    refine ⟨held_sub lah (by omega) (by omega), by simp only [AW, Apart]; omega, ?_, ?_, fun e he => by simp at he⟩
    · have := hsu; simp only [Apart, stUp] at this ⊢; omega
    · simp only [stUp, Apart]; rw [hW3, hcap3]; omega
  refine reaches_mono (xjStep impl hap R hclr hmv hmk hSN nsD stkD costD hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL hserv
    ret hret b L g sp K n mp mc Mv (stW M st + 8 * l0) n Xv yp ylen Y yi zp zc st n0 (l0 + StackNat.rnd n) M3 r18 r29
    hKD hKL hB4 (by rw [hlen3, hlen]) hx3 hxO3 (by rw [hv, hxv]) (by omega) hmB hMo hM1 (by omega) hbud hI
    S3 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13) (isReturn_mono fun s' h => ?_)
  obtain ⟨zzp, zzc, h⟩ := h
  exact ⟨l0 + StackNat.rnd n, zzp, zzc, by omega, h⟩

end FvModexp.Arm64.W4Pro
