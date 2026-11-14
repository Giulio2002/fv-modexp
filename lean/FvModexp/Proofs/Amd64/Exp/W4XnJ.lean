import FvModexp.Proofs.Amd64.Exp.W4XnB
import FvModexp.Proofs.Amd64.Exp.W4XnK
import FvModexp.Proofs.Amd64.Exp.W4Xj

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the `x` join `j300` to the function's `RET` (agent expmc s55; twin of `Arm64.W4XnJ`)

* `keeps_xb`: the copy/clear step of path B (`xnB`) keeps `CtxX`;
* `xnBStep`: path B from the entry of `rr := stk.nat(n)` (after `xnJ`'s spills): the call, `xnB`, the context raised
  to the new stack level with `x := rr`, then `xjStep`;
* `xnJStep`: from `j300` (`len x ≤ n`): path C (`len x = n`, `x` installed as it is) or path B.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- the budget `xjStep` needs from `xJ` on (stack level `l`) -/
@[reducible] def xjBud (n costD l : Nat) : Nat :=
  stackNatCost l (2 * n) + (makeCost (1 + 128 * n / 64 + 1) +
    (stackNatCost (l + StackNat.rnd (2 * n)) (2 * n) + (costD + (blockSize (8 * n) true +
    stackNatCost (l + 2 * StackNat.rnd (2 * n)) (17 * n) + 2 * blockSize (8 * (2 * n + 4)) true))))

/-- the stack-length and division-cost conditions `xjStep` needs at level `l` -/
@[reducible] def XjL (costF : Nat → Nat → Nat → Nat) (n costD l : Nat) : Prop :=
  l + StackNat.rnd (2 * n) + 2 * n + 3 ≤ 2 ^ 16 ∧ l + 2 * StackNat.rnd (2 * n) + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16 ∧
  l + 2 * StackNat.rnd (2 * n) + 17 * n + 3 ≤ 2 ^ 16 ∧ costF (l + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD

/-- the post of path B (`M` before `xnJ`'s spills; `X` the value of `x`) -/
@[reducible] def XnBQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M3 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
    KeepsX R L L2 g fs sp K st l0 [] M M3 ∧ b - stackNatCost l0 n ≤ b2 ∧ stLen M3 st = l0 + StackNat.rnd n ∧
    XjQ R b2 costD L2 g fs sp K n mp Mv yp ylen Y yi zp zc st n0 (l0 + StackNat.rnd n) fbp X M3 s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the copy/clear step of path B keeps the context -/
theorem keeps_xb {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {M M' : Memory}
    (hC : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [] M)
    (hrin : l0 + n ≤ stLen M st)
    (hF : MemFrame M M' (R.rt ++ xbW sp (stW M st + 8 * l0) n))
    (hL : LiveFrame M M' L [(stW M st + 8 * l0, stW M st + 8 * l0 + 8 * n)]) (hrg : M'.regions = M.regions) :
    KeepsX R L L g fs sp K st l0 [] M M' ∧ stLen M' st = stLen M st ∧ stW M' st = stW M st ∧
      stCap M' st = stCap M st := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hsth, hstw, hsok, -, hl0, hcap, -, hug, huf, huw, hsu, hstg, hstf, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, hga, -, -, -, -, -, -, -, -, -, f6⟩ := hce0
  have hsok0 := hsok
  obtain ⟨-, -, hstacc, -, hlive, hlc, -⟩ := hsok0
  obtain ⟨-, lah, laacc, -⟩ := hlive hcap
  simp only [AW, Apart, stUp] at hstw huw hug huf hsu hga hstg hstf f6
  have ow : ∀ a k, (a + k ≤ sp - 8 - K ∨ sp + 0x3c0 ≤ a) →
      (a + k ≤ stW M st + 8 * l0 ∨ stW M st + 8 * l0 + 8 * n ≤ a) → Outside a k (xbW sp (stW M st + 8 * l0) n) := by
    intro a k h1 h2; simp only [xbW, outside_cons, outside_nil, and_true]; omega
  have rdh : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → (a + k ≤ sp - 8 - K ∨ sp + 0x3c0 ≤ a) →
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
  refine keeps_ofX hce (LiveExt.refl R L) hF hL hrg ?_ ?_ ?_ ?_ ?_ hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _)
    (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
    (arrIn_kept ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
  · clear hstw huw hug huf hsu hga hstg hstf f6
    intro q hq hlt
    simp only [xbW, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hsu hstf f6 huf
    simp only [xbW, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hsu hga hstg hug
    simp only [xbW, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf f6
    intro a k' ho
    obtain ⟨-, o2, -, o4, -⟩ := ho
    simp only [AW, Apart, stUp] at o2 o4
    refine ⟨ow _ _ (by omega) (by omega), ?_⟩
    simp only [outside_cons, outside_nil, and_true]
    omega
  · clear hug huf hsu hga hstg hstf f6
    intro j hj
    simp only [KeptJX] at hj
    simp only [xbW, outside_cons, outside_nil, and_true]; omega

theorem xbWs_in (sp : Nat) : ∀ q ∈ xbWs sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 := by
  intro q hq
  simp only [xbWs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem xbWs_in' (sp : Nat) : ∀ q ∈ xbWs sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2 := by
  intro q hq
  simp only [xbWs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem xbWs_kept (sp : Nat) : ∀ j, KeptJX j → Outside (sp + j) 8 (xbWs sp) := by
  intro j hj
  simp only [KeptJX] at hj
  simp only [xbWs, outside_cons, outside_nil, and_true]
  omega

/-- the invariant survives own stores inside the frame -/
theorem inv_own {R : RtInv} {b g sp K : Nat} {L ws : List (Nat × Nat)} {M M1 : Memory}
    (hF : MemFrame M M1 ws) (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2)
    (hrt : Outside (sp - 8 - K) (K + 968) R.rt) (hK : K + 8 ≤ sp)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L M1) := by
  refine FvModexp.Expmc.inv_frame hF (fun q hq => Or.inr ?_) h
  have := hin q hq
  exact hrt.of_sub (by omega) (by omega)

/-- the facts of the context the `x` normalisation's steps use -/
theorem CtxX.nb {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) :
    Env R L g fs sp M ∧ 41512 ≤ K ∧ StkOK M R L st ∧ 0 < stCap M st ∧ l0 ≤ stLen M st ∧
    AW sp K (stUp M st l0).1 (stUp M st l0).2 ∧ Apart (stUp M st l0).1 (stUp M st l0).2 (g + 16) 8 ∧
    Apart (stUp M st l0).1 (stUp M st l0).2 (fs - 8) 8 ∧
    M.accessible (sp + 0x3c0) 0x20 false = true ∧ Outside (sp + 0x3c0) 0x20 R.rt ∧
    Apart (sp + 0x3c0) 0x20 (stUp M st l0).1 (stUp M st l0).2 ∧
    M.readLE (sp + 0x3b0) 8 = n ∧ M.readLE (sp + 0x3c0) 8 = zp ∧ M.readLE (sp + 0x3d0) 8 = zc ∧
    M.readLE (sp + 0x3d8) 8 = st := by
  obtain ⟨he, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsok, -, hl0, hcap, -, hug, huf, huw, -, -, -, -, -, -, -,
    hcacc, hcrt, hcO, -, r3b0, -, r3d0, r3c0, -, -, r3d8, -⟩ := h
  exact ⟨he, hK, hsok, hcap, hl0, huw, hug, huf, hcacc, hcrt, hcO.2.2.2.1, r3b0, r3c0, r3d0, r3d8⟩

theorem aw_free {sp K st l0 : Nat} {M : Memory} (huw : AW sp K (stUp M st l0).1 (stUp M st l0).2)
    (hl : l0 ≤ stLen M st) (hlc : stLen M st ≤ stCap M st) : AW sp K (stFree M st).1 (stFree M st).2 := by
  simp only [AW, Apart, stUp, stFree] at huw ⊢; omega

theorem rnd_ge (n : Nat) : n ≤ StackNat.rnd n := by simp only [StackNat.rnd]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path B from the entry of `rr := stk.nat(n)` (return `bSnRet`; `M` = the memory before `xnJ`'s spills) to `RET` -/
theorem xnBStep (hRR : FvModexp.Amd64.W4Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W4Loop.fn = false)
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsWL : nsL.contains W4Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp0 Xv0 xp xl xr yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : CtxX R L g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r [] M) (hl0e : stLen M st = l0)
    (hx : XIn R L sp K st l0 M xp xl xr) (hxl : xl < n) (hfbp : fbp < 2 ^ 64)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hL1 : XjL costF n costD (l0 + StackNat.rnd n))
    (hbud : stackNatCost l0 n + xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 snE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hmf : MemFrame M S.mem (xbWs sp)) (hrg : S.mem.regions = M.regions)
    (q8 : S.mem.readLE (sp - 8) 8 = bSnRet) (q130 : S.mem.readLE (sp + 0x130) 8 = xl)
    (q368 : S.mem.readLE (sp + 0x368) 8 = xp)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XnBQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp (M.readLE xp (8 * xl)) M) := by
  obtain ⟨hal, hsp1, hsp2, hacc, -, -, -, hn, hn128, -, -, -, -, hst48, hstw, hrt, hK8⟩ := CtxX.xj hC
  obtain ⟨hs0, hs1, hs2, hcF⟩ := hL1
  -- the spills
  have hk0 := keeps_ownX hC hmf hrg (xbWs_in sp) (xbWs_kept sp)
  have hC1 := CtxX.keep hC hk0
  have hlen1 : stLen S.mem st = l0 := by
    simp only [AW, Apart] at hstw
    rw [← hl0e]; exact hmf.readLE _ _ (outside_ws_of_win (lo := sp - 8) (hi := sp + 0x3c0) (by omega) (xbWs_in sp))
  have hinv1 := inv_own hmf (xbWs_in' sp) hrt hK8 hinv
  have hcap1 : l0 ≤ stCap S.mem st := by have := hk0.2.2.2.2.2.2.2.1.2.2.2.2.2.1; omega
  have hx1 := XIn.keep hx hk0 hcap1
  have hrn := rnd_ge n
  have hpre : SnPre R b L g fs sp st n S.mem :=
    snPre_ofX hC1 hserv (by omega) (by rw [hlen1]; omega) (by rw [hlen1]; omega) hinv1
  refine snCallR hap hSN 0x325 (by decide) S hpre (by omega) hpc hsp (by rw [q8]) h0 h3 rfl h14 hfs hx15 hdf
    (fun S2 L2 b2 gpc gsp g5 g14 gfs gx gdf gX0 gX3 gX1 hS => ?_)
  have hk2 := keeps_snX hC1 hn hS
  have hC2 := CtxX.keep hC1 hk2
  have hS0 := hS
  obtain ⟨-, hb2, hinv2, hsok2, hlen2, -, -, -, -, -, -⟩ := hS0
  rw [hlen1] at hlen2 hb2
  have hlc2 := hsok2.2.2.2.2.2.1
  have hcap2 : l0 ≤ stCap S2.mem st := by simp only [stLen, stCap] at hlen2 hlc2 ⊢; omega
  have hx2 := XIn.keep hx1 hk2 hcap2
  obtain ⟨he1, hK, hsok1, -, hl01, huw1, -, -, -, -, -, -, -, -, -⟩ := CtxX.nb hC1
  have hfree1 := aw_free huw1 hl01 hsok1.2.2.2.2.2.1
  have r130 : S2.mem.readLE (sp + 0x130) 8 = xl := by
    rw [slot_sn hS hrt (by omega) hK8 hstw hfree1 0x130 (by omega) (by omega)]; exact q130
  have r368 : S2.mem.readLE (sp + 0x368) 8 = xp := by
    rw [slot_sn hS hrt (by omega) hK8 hstw hfree1 0x368 (by omega) (by omega)]; exact q368
  obtain ⟨he2, -, hsok2', hcap2', hl02, huw2, hug2, huf2, hcacc2, hcrt2, hcu2, r3b0, r3c0, r3d0, r3d8⟩ :=
    CtxX.nb hC2
  have hc := codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive64.of_codeIn hc hmv
  have hclrL := MemclrNoHeapPointersLive64.of_codeIn hc hclr
  obtain ⟨hxl', hxr0, hxr40, hxa, hx48, ⟨o1, o2, o3, o4, -⟩⟩ := hx2
  have hsok20 := hsok2
  obtain ⟨-, -, -, -, hlive, -, -⟩ := hsok20
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap2'
  have hrin : l0 + n ≤ stLen S2.mem st := by simp only [stLen] at hlen2 ⊢; omega
  have u1 := huw2; have u2 := o2; have u3 := o4; have u4 := hug2; have u5 := hcu2
  simp only [AW, Apart, stUp] at u1 u2 u3 u4 u5
  refine xnB impl hmvL hclrL b2 L2 g fs sp n xp xl (stW S2.mem st + 8 * l0) st zp zc S2.mem he2 hn128 hxl
    (S2.mem.accessible_sub hxa (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega) (by unfold Apart; omega)
    (S2.mem.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)) (by omega)
    (held_sub lah (by omega) (by omega)) (by unfold Apart; omega) (by unfold Apart; omega) (by omega)
    (by unfold Apart; omega) (hserv.2.1 _ _ _ (by omega)) (hserv.2.2.1 _ _ (by omega)) hinv2 hcacc2 hcrt2
    (by unfold Apart; omega) r3b0 r130 r368 r3d8 r3c0 r3d0
    S2 gpc gsp rfl (by rw [gX0 hn, hlen1]) gX1 g14 gfs gx gdf
    (fun S3 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 hF hL hI hrg3 hv => ?_)
  obtain ⟨hk3, hlen3, hW3, hcap3⟩ := keeps_xb hC2 hrin hF hL hrg3
  have hC3 := CtxX.keep hC2 hk3
  have hrn' : l0 + StackNat.rnd n ≤ stLen S3.mem st := by rw [hlen3]; simp only [stLen] at hlen2 ⊢; omega
  have hC4 := CtxX.raise hC3 (l1 := l0 + StackNat.rnd n) (by omega) hrn'
  have hsth2 := hsok2.2.1
  have hrInp : Inp R L2 sp n S3.mem (stW S2.mem st + 8 * l0) :=
    ⟨by rw [hF.accessible]; exact S2.mem.accessible_sub laacc (Or.inl rfl) (by omega) (by omega), by omega,
      held_sub lah (by omega) (by omega), by unfold Apart; omega⟩
  have hsu2 : Apart st 24 (stUp S2.mem st l0).1 (stUp S2.mem st l0).2 := by
    have := hC2; obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, h36, -⟩ := this
    exact h36
  have hrO : Obj R L2 sp K st (l0 + StackNat.rnd n) [] S3.mem (stW S2.mem st + 8 * l0) (8 * n) := by
    refine ⟨held_sub lah (by omega) (by omega), by simp only [AW, Apart]; omega, ?_, ?_, fun e he => by simp at he⟩
    · simp only [Apart, stUp] at hsu2 ⊢; omega
    · simp only [stUp, Apart]; rw [hW3, hcap3]; omega
  have hxv : S2.mem.readLE xp (8 * xl) = M.readLE xp (8 * xl) :=
    (hk2.2.2.2.1 _ _ (obj_subk hx1.2.2.2.2.2 (Nat.le_refl _) (by omega))).trans
      (hk0.2.2.2.1 _ _ (obj_subk hx.2.2.2.2.2 (Nat.le_refl _) (by omega)))
  have hC5 := CtxX.setX hC4 hrInp hrO (hv.trans hxv)
  have hlenE : stLen S3.mem st = l0 + StackNat.rnd n := by rw [hlen3, hlen2]
  refine ReachesRet.mono (xjStep hRR hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC5 hlenE
    (by omega) hfbp hmB hMo hM1 hs0 hs1 hs2 hcF (bud2 hbud hb2) hI S3 k1 k2 rfl k3 k4 k5 k6 k7 k8 k9 k10 k11)
    (fun s' h => ⟨S3.mem, L2, b2, (hk0.trans hk2 hcap1).trans hk3 hcap2, hb2, hlenE, h⟩)

/-- the post from the `x` join on: path C (`len x = n`) or path B -/
@[reducible] def XnJQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X : Nat) (M : Memory) (s' : State) : Prop :=
  XjQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X M s' ∨
    XnBQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X M s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `x` join `j300` (`len x ≤ n`) to the function's `RET` -/
theorem xnJStep (hRR : FvModexp.Amd64.W4Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W4Loop.fn = false)
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsWL : nsL.contains W4Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp0 Xv0 xp xl xr xc yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : CtxX R L g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r [] M) (hl0e : stLen M st = l0)
    (hx : XIn R L sp K st l0 M xp xl xr) (hxln : xl ≤ n) (hxc : xc < 2 ^ 64) (hfbp : fbp < 2 ^ 64)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hL0 : XjL costF n costD l0) (hL1 : XjL costF n costD (l0 + StackNat.rnd n))
    (hb0 : xjBud n costD l0 ≤ b) (hbud : stackNatCost l0 n + xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 j300) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XnJQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp (M.readLE xp (8 * xl)) M) := by
  obtain ⟨hal, hsp1, hsp2, hacc, -, -, -, hn, hn128, -, -, -, -, hst48, hstw, hrt, hK8⟩ := CtxX.xj hC
  have hx0 := hx
  obtain ⟨-, -, hxr40, -, hx48, -⟩ := hx0
  refine xnJ hsp1 hsp2 hacc hn128 (by omega) (by omega) (by omega) S hpc hsp hmem h6 h8 h3 h7
    (fun hc S' e1 e2 e3 e4 e5 e6 => ?_) (fun hc S' e1 e2 e3 e4 e5 e6 e7 e8 e9 hmf hrg q8 q130 q368 => ?_)
  · obtain rfl : xl = n := by omega
    obtain ⟨hs0, hs1, hs2, hcF⟩ := hL0
    have hC' := CtxX.ofXIn hC hx
    refine ReachesRet.mono (xjStep hRR hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC' hl0e
      hxc hfbp hmB hMo hM1 hs0 hs1 hs2 hcF hb0 hinv S' e1 (by rw [e3]; exact hsp) e2
      (by rw [e3]; exact h6) (by rw [e3]; exact h8) (by rw [e3]; exact h9) (by rw [e3]; exact h7)
      (by rw [e3]; exact h3) (by rw [e3]; exact h14) (by rw [e4]; exact hfs) (by rw [e5]; exact hx15)
      (by rw [e6]; exact hdf)) (fun s' h => Or.inl h)
  · refine ReachesRet.mono (xnBStep hRR hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC hl0e
      hx hc hfbp hmB hMo hM1 hL1 hbud hinv S' e1 e2 hmf hrg q8 q130 q368
      e3 e4 (by rw [e6]; exact h14) (by rw [e7]; exact hfs) (by rw [e8]; exact hx15) (by rw [e9]; exact hdf))
      (fun s' h => Or.inr h)

end FvModexp.Amd64.W4Pro
