import FvModexp.Proofs.Amd64.Exp.W4XnA2

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the whole `x` normalisation from `xnE` (fn+0x216) to the function's `RET`
(agent expmc s56; twin of `Arm64.W4XnS`)

* `xnAStep` (path A, `len x > n`): the return-address push, `q := stk.nat(len x - n + 1)` (`snCallR`, return
  fn+0x22e), `xnA1` (spills of `q`), `z2 := stk.nat(n)` (return fn+0x25b), then `xnA2K` (division, `x := x mod m`,
  join);
* `xnStep`: `xnSplit`, then the join `xnJStep` (`len x ≤ n`, `x` as given) or path A.
Posts: `XnAQ` (path A: two `KeepsX` steps — before and after `q` is an extra context range — then `XnA2Q`) and
`XnQ := (xl ≤ n ∧ XnJQ) ∨ (n < xl ∧ XnAQ)` (the branch condition is kept for the value bound); every `KeepsX` is at the entry level `l0`, the scratch `q` is a stack nat above it (the
`Anc` bridge, `W4Anc`, consumes exactly these facts).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- the post of path A (`M` at `xnE`; `k = len x - n + 1`, `X` the value of `x`) -/
@[reducible] def XnAQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp k X : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat) (M4 : Memory) (L4 : List (Nat × Nat)) (b4 : Nat),
    KeepsX R L L2 g fs sp K st l0 [] M M2 ∧ stLen M2 st = l0 + StackNat.rnd k ∧ b - stackNatCost l0 k ≤ b2 ∧
    KeepsX R L2 L4 g fs sp K st l0 [(stW M2 st + 8 * l0, 8 * k)] M2 M4 ∧
    b2 - stackNatCost (l0 + StackNat.rnd k) n ≤ b4 ∧ stLen M4 st = l0 + StackNat.rnd k + StackNat.rnd n ∧
    XnA2Q R b4 costD L4 g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp (stW M2 st + 8 * l0) k X M4 s'

/-- the post of the `x` normalisation (`M` at `xnE`) -/
@[reducible] def XnQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp xl X : Nat) (M : Memory) (s' : State) : Prop :=
  (xl ≤ n ∧ XnJQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp X M s') ∨
    (n < xl ∧ XnAQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp (xl - n + 1) X M s')

theorem w0_in (sp : Nat) : ∀ q ∈ [(sp - 8, sp)], sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 := by
  intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact ⟨Nat.le_refl _, by omega⟩

theorem w0_in' (sp : Nat) : ∀ q ∈ [(sp - 8, sp)], sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2 := by
  intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact ⟨Nat.le_refl _, by omega, by omega⟩

theorem w0_kept (sp : Nat) : ∀ j, KeptJX j → Outside (sp + j) 8 [(sp - 8, sp)] := by
  intro j hj; simp only [KeptJX] at hj; simp only [outside_cons, outside_nil, and_true]; omega

theorem xa1_in (sp : Nat) : ∀ q ∈ xa1Ws sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 := by
  intro q hq; simp only [xa1Ws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem xa1_in' (sp : Nat) : ∀ q ∈ xa1Ws sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2 := by
  intro q hq; simp only [xa1Ws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem xa1_kept (sp : Nat) : ∀ j, KeptJX j → Outside (sp + j) 8 (xa1Ws sp) := by
  intro j hj; simp only [KeptJX] at hj; simp only [xa1Ws, outside_cons, outside_nil, and_true]; omega

/-- the stack header is not in an own-store window -/
theorem hdr_win {M M' : Memory} {sp K st : Nat} {ws : List (Nat × Nat)} (hF : MemFrame M M' ws)
    (hin : ∀ q ∈ ws, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0) (h : AW sp K st 24) (hK : K + 8 ≤ sp) :
    stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st := by
  simp only [AW, Apart] at h
  exact ⟨hF.readLE _ _ (outside_ws_of_win (by omega) hin), hF.readLE _ _ (outside_ws_of_win (by omega) hin),
    hF.readLE _ _ (outside_ws_of_win (by omega) hin)⟩

set_option maxRecDepth 20000 in
theorem CtxX.arr {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) :
    0 < stCap M st ∧ AW sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧
      Apart (stW M st) (8 * stCap M st) (fs - 8) 8 ∧ Apart st 24 (stUp M st l0).1 (stUp M st l0).2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap,
    harr, -, -, -, hsu, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact ⟨hcap, (harr hcap).1, (harr hcap).2.1, (harr hcap).2.2, hsu⟩

theorem budA3 {b b2 b4 x y z : Nat} (h : x + (y + z) ≤ b) (h2 : b - x ≤ b2) (h4 : b2 - y ≤ b4) : z ≤ b4 := by omega

theorem bud1 {b x y : Nat} (h : x + y ≤ b) : x ≤ b := by omega

theorem bud2' {b b2 x y z : Nat} (h : x + (y + z) ≤ b) (h2 : b - x ≤ b2) : y ≤ b2 := by omega

/-- a sub-range of `q` (inside the stack's array) is apart from what the array is apart from -/
theorem q_sub {W c l0 k qp a b : Nat} (hq : qp = W + 8 * l0) (hin : 8 * l0 + 8 * k ≤ 8 * c)
    (h : Apart W (8 * c) a b) : Apart qp (8 * k) a b := by
  subst hq; unfold Apart at h ⊢; omega

theorem q_st {W c l0 k qp st : Nat} (hq : qp = W + 8 * l0) (hin : 8 * l0 + 8 * k ≤ 8 * c)
    (h : Apart st 24 (W + 8 * l0) (8 * (c - l0))) : Apart qp (8 * k) st 24 := by
  subst hq; unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path A from `stk.nat`'s entry (the first call, `k = len x - n + 1`; `M` the memory at `xnE`) to the `RET` -/
theorem xnAStep (hRR : FvModexp.Amd64.W4Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r xp xl xc : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : CtxX R L g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r [] M) (hl0e : stLen M st = l0)
    (hx : XIn R L sp K st l0 M xp xl xc) (hxN : NatNorm M xp xl) (hxl : n < xl) (hxl9 : xl ≤ 2 ^ 9)
    (hxs : Obj R L sp K st l0 [] M (sp + 0x3e0) 0x18) (hacc2 : M.accessible (sp + 0x3c0) 0x38 false = true)
    (r3e0 : M.readLE (sp + 0x3e0) 8 = xp) (r3e8 : M.readLE (sp + 0x3e8) 8 = xl) (r3f0 : M.readLE (sp + 0x3f0) 8 = xc)
    (hfbp : fbp < 2 ^ 64) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + 64 ≤ 2 ^ 16)
    (hcX : costF (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n ≤ costD)
    (hL0 : XjL costF n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n))
    (hL1 : XjL costF n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n))
    (hbA : stackNatCost l0 (xl - n + 1) + (stackNatCost (l0 + StackNat.rnd (xl - n + 1)) n +
      (costD + xjBud n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n))) ≤ b)
    (hbB : stackNatCost l0 (xl - n + 1) + (stackNatCost (l0 + StackNat.rnd (xl - n + 1)) n +
      (costD + (stackNatCost (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
        xjBud n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n)))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 snE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 (xl - n + 1))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hmem : S.mem = M.writeLE (sp - 8) 8 aSn1Ret) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XnAQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp (xl - n + 1) (M.readLE xp (8 * xl)) M) := by
  obtain ⟨-, hsp1, hsp2, hacc, -, -, -, hn, hn128, -, -, -, -, hst48, hstw, hrt, hK8⟩ := CtxX.xj hC
  obtain ⟨k, hkdef⟩ : ∃ k, k = xl - n + 1 := ⟨_, rfl⟩
  rw [← hkdef] at hsl hcX hL0 hL1 hbA hbB h3 ⊢
  have hk0 : 0 < k := by omega
  have hk40 : k < 2 ^ 40 := by omega
  have hrk := rnd_ge k
  have hrn := rnd_ge n
  -- the return-address push
  have hmf0 : MemFrame M S.mem [(sp - 8, sp)] := by
    rw [hmem]
    exact (MemFrame.refl _ _).writeLE_inRanges _ ⟨(sp - 8, sp), List.mem_singleton_self _, Nat.le_refl _, by omega⟩
  have hrg0 : S.mem.regions = M.regions := by rw [hmem]; simp only [Janus.Arm64.Memory.regions_writeLE]
  have hk1 := keeps_ownX hC hmf0 hrg0 (w0_in sp) (w0_kept sp)
  have hC1 := CtxX.keep hC hk1
  have hlen1 : stLen S.mem st = l0 := by rw [← hl0e]; exact (hdr_win hmf0 (w0_in sp) hstw hK8).2.1
  have hinv1 := inv_own hmf0 (w0_in' sp) hrt hK8 hinv
  have hpre1 : SnPre R b L g fs sp st k S.mem :=
    snPre_ofX hC1 hserv (by omega) (by rw [hlen1]; omega) (by rw [hlen1]; exact bud1 hbA) hinv1
  -- `q := stk.nat(k)`
  refine snCallR hap hSN 0x22e (by decide) S hpre1 (by omega) hpc hsp
    (by rw [hmem, readLE_writeLE_same _ _ _ rfl]; rfl) h0 h3 rfl h14 hfs hx15 hdf
    (fun S2 L2 b2 gpc gsp g5 g14 gfs gx gdf gX0 gX3 gX1 hS => ?_)
  have hk2 := keeps_snX hC1 hk0 hS
  have hC2 := CtxX.keep hC1 hk2
  have hS0 := hS
  obtain ⟨hx2, hb2, hinv2, hsok2, hlen2, -, -, -, -, -, -⟩ := hS0
  rw [hlen1] at hlen2 hb2 gX0
  have hlc2 := hsok2.2.2.2.2.2.1
  obtain ⟨hcap2, harr2, hag2, haf2, hsu2⟩ := CtxX.arr hC2
  obtain ⟨q8, qH, qacc, q48⟩ := hsok2.2.2.2.2.1 hcap2
  obtain ⟨qp, hqp⟩ : ∃ qp, qp = stW S2.mem st + 8 * l0 := ⟨_, rfl⟩
  have hqc : 8 * l0 + 8 * k ≤ 8 * stCap S2.mem st := by simp only [stLen, stCap] at hlen2 hlc2 ⊢; omega
  have hqin : stW S2.mem st + 8 * l0 ≤ (qp, 8 * k).1 ∧ (qp, 8 * k).1 + (qp, 8 * k).2 ≤ stW S2.mem st + 8 * stCap S2.mem st := by
    simp only; omega
  have hl02 : l0 ≤ stCap S2.mem st := by omega
  have hl01 : l0 ≤ stCap S.mem st := by have := hsok2; rw [← hlen1]; exact hk1.2.2.2.2.2.2.2.1.2.2.2.2.2.1
  have K12 := hk1.trans hk2 hl01
  have hC2' := CtxX.addEx hC2 hqin
  -- the spills of `q`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, s3b0, -, -, s3d8⟩ := CtxX.nb hC2
  have hacc2' : ∀ a k w, S2.mem.accessible a k w = M.accessible a k w := K12.2.1
  refine xnA1 (qp := qp) (ql := k) (qc := k) hsp1 hsp2 (by rw [hacc2']; exact hacc) hn128 (by rw [hacc2']; exact hacc2) (by omega) (by omega) (by omega)
    s3d8 s3b0 S2 gpc gsp rfl (by rw [gX0 hk0, ← hqp]) gX3 gX1
    (fun S3 c1 c2 c3 c4 c5 c6 c7 c8 c9 hmf3 hrg3 q8' q370 q140 q138 => ?_)
  have hk3 := keeps_ownX hC2' hmf3 hrg3 (xa1_in sp) (xa1_kept sp)
  have hC3 := CtxX.keep hC2' hk3
  obtain ⟨eW3, eL3, eC3⟩ := hdr_win hmf3 (xa1_in sp) hstw hK8
  have hinv3 := inv_own hmf3 (xa1_in' sp) hrt hK8 hinv2
  have hpre3 : SnPre R b2 L2 g fs sp st n S3.mem :=
    snPre_ofX hC3 hserv (by omega) (by rw [eL3, hlen2]; omega) (by rw [eL3, hlen2]; exact bud2' hbA hb2) hinv3
  -- `z2 := stk.nat(n)`
  refine snCallR hap hSN 0x25b (by decide) S3 hpre3 (by omega) c1 c2 (by rw [q8']) c3 c4 rfl
    (by rw [c6, g14]) (by rw [c7]; exact gfs) (by rw [c8]; exact gx) (by rw [c9]; exact gdf)
    (fun S4 L4 b4 hpc4 hsp4 g5' g14' gfs' gx' gdf' gX0' gX3' gX1' hS4 => ?_)
  have hk4 := keeps_snX hC3 hn hS4
  have hC4 := CtxX.keep hC3 hk4
  have hS40 := hS4
  obtain ⟨hx4, hb4, hinv4, hsok4, hlen4, -, -, -, -, -, -⟩ := hS40
  rw [eL3, hlen2] at hlen4 hb4
  have hl03 : l0 ≤ stCap S3.mem st := by rw [eC3]; exact hl02
  have K34 := hk3.trans hk4 hl03
  -- `q` at the division
  have hqH : Held R L2 qp (8 * k) := held_sub qH (by omega) (by omega)
  obtain ⟨hqB, hqz⟩ := below_sn (l0 := l0) hS4 hqH
    (Or.inl ⟨by rw [eW3]; omega, by rw [eW3, eL3, hlen2]; omega⟩)
  rw [eL3, hlen2] at hqz gX0'
  have hqL : NatLive S4.mem R L4 qp k := fun _ =>
    ⟨by rw [hqp]; omega, hx4.held hqH,
      by rw [K34.2.1]; exact S2.mem.accessible_sub qacc (Or.inr rfl) (by omega) (by omega), by omega⟩
  -- `x` and its argument slots
  obtain ⟨hxlc, -, hxc40, hxa, hx48, hxO⟩ := hx
  have hxO1 : Obj R L sp K st l0 [] M xp (8 * xl) := obj_subk hxO (Nat.le_refl _) (by omega)
  have hxO2 := obj_addEx (obj_keepX K12 hl02 hxO1) hqin
  have hxs2 := obj_addEx (obj_keepX K12 hl02 hxs) hqin
  have hl04 : l0 ≤ stCap S4.mem st := by have := hsok4.2.2.2.2.2.1; simp only [stLen, stCap] at hlen4 this ⊢; omega
  have hxO4 := obj_keepX K34 hl04 hxO2
  have rd : ∀ a c, sp + 0x3e0 ≤ a → a + c ≤ sp + 0x3e0 + 0x18 → S4.mem.readLE a c = M.readLE a c := fun a c h1 h2 => by
    rw [K34.2.2.2.1 _ _ (obj_subk hxs2 h1 h2), K12.2.2.2.1 _ _ (obj_subk hxs h1 h2)]
  have xval : S4.mem.readLE xp (8 * xl) = M.readLE xp (8 * xl) := by
    rw [K34.2.2.2.1 _ _ hxO2, K12.2.2.2.1 _ _ hxO1]
  -- the slots written by `xnA1` survive `stk.nat(n)`
  obtain ⟨-, hK41, hsok3, -, hl03', huw3, -, -, -, -, -, -, -, -, -⟩ := CtxX.nb hC3
  have hfree3 := aw_free huw3 hl03' hsok3.2.2.2.2.2.1
  have sl : ∀ j, 16 ≤ j → j + 8 ≤ 0x3c0 → S4.mem.readLE (sp + j) 8 = S3.mem.readLE (sp + j) 8 :=
    fun j a c => slot_sn hS4 hrt (by omega) hK8 hstw hfree3 j a c
  refine ReachesRet.mono (xnA2K hRR hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL (xp := xp) (xl := xl)
    (xc := xc) hKD hKL hC4 hlen4 rfl hk0 hk40 hqL
    (q_sub hqp hqc harr2) (q_sub hqp hqc hag2) (q_sub hqp hqc haf2) (q_st hqp hqc hsu2) hqB hqz hxO4
    (by rw [K34.2.1, K12.2.1]; exact M.accessible_sub hxa (Or.inl rfl) (Nat.le_refl _) (by omega)) (by omega)
    (norm_keep K34.2.2.2.1 hxO2 (norm_keep K12.2.2.2.1 hxO1 hxN)) hxl9 (by omega)
    (by rw [K34.2.1, K12.2.1]; exact hacc2)
    (by rw [rd _ _ (Nat.le_refl _) (by omega)]; exact r3e0) (by rw [rd _ _ (by omega) (by omega)]; exact r3e8)
    (by rw [rd _ _ (by omega) (by omega)]; exact r3f0)
    (by rw [sl 0x370 (by omega) (by omega)]; exact q370) (by rw [sl 0x140 (by omega) (by omega)]; exact q140)
    (by rw [sl 0x138 (by omega) (by omega)]; exact q138)
    hfbp hmB hMo hM1 (by rw [hlen4]; exact hsl) (by rw [hlen4]; exact hcX) (by rw [hlen4]; exact hL0)
    (by rw [hlen4]; exact hL1) (by rw [hlen4]; exact budA3 hbA hb2 hb4) (by rw [hlen4]; exact budA3 hbB hb2 hb4) hinv4
    S4 hpc4 hsp4 rfl (gX0' hn) gX3' gX1' g14' gfs' gx' gdf')
    (fun s' h => ⟨S2.mem, L2, b2, S4.mem, L4, b4, K12, hlen2, hb2, by rw [← hqp]; exact K34, hb4, hlen4, ?_⟩)
  rw [xval, hqp] at h
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the whole `x` normalisation from `xnE` (fn+0x216) to the function's `RET` (`M` at `xnE`, `x` as given) -/
theorem xnStep (hRR : FvModexp.Amd64.W4Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r xp xl xc : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : CtxX R L g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r [] M) (hl0e : stLen M st = l0)
    (hx : XIn R L sp K st l0 M xp xl xc) (hxN : NatNorm M xp xl) (hxl9 : xl ≤ 2 ^ 9)
    (hxs : Obj R L sp K st l0 [] M (sp + 0x3e0) 0x18) (hacc2 : M.accessible (sp + 0x3c0) 0x38 false = true)
    (r3e0 : M.readLE (sp + 0x3e0) 8 = xp) (r3e8 : M.readLE (sp + 0x3e8) 8 = xl) (r3f0 : M.readLE (sp + 0x3f0) 8 = xc)
    (hfbp : fbp < 2 ^ 64) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hLC0 : XjL costF n costD l0) (hLC1 : XjL costF n costD (l0 + StackNat.rnd n))
    (hbC0 : xjBud n costD l0 ≤ b) (hbC1 : stackNatCost l0 n + xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hsl : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + 64 ≤ 2 ^ 16)
    (hcX : costF (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n ≤ costD)
    (hL0 : XjL costF n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n))
    (hL1 : XjL costF n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n))
    (hbA : stackNatCost l0 (xl - n + 1) + (stackNatCost (l0 + StackNat.rnd (xl - n + 1)) n +
      (costD + xjBud n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n))) ≤ b)
    (hbB : stackNatCost l0 (xl - n + 1) + (stackNatCost (l0 + StackNat.rnd (xl - n + 1)) n +
      (costD + (stackNatCost (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
        xjBud n costD (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n)))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xnE) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XnQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp xl (M.readLE xp (8 * xl)) M) := by
  obtain ⟨-, hsp1, hsp2, hacc, -, -, -, -, hn128, -, -, -, -, hst48, -, -, -⟩ := CtxX.xj hC
  have hxc40 := hx.2.2.1
  have hxlc := hx.1
  refine xnSplit hsp1 hsp2 hacc hn128 (by omega) (by omega) S hpc hsp hmem h8 h3 h7
    (fun hc S' e1 e2 e3 e4 e5 e6 => ?_) (fun hc S' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 => ?_)
  · refine ReachesRet.mono (xnJStep hRR hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL (xc := xc) hKD hKL
      hC hl0e
      hx hc (by omega) hfbp hmB hMo hM1 hLC0 hLC1 hbC0 hbC1 hinv S' e1 (by rw [e3]; exact hsp) e2
      (by rw [e3]; exact h6) (by rw [e3]; exact h8) (by rw [e3]; exact h9) (by rw [e3]; exact h7) (by rw [e3]; exact h3)
      (by rw [e3]; exact h14) (by rw [e4]; exact hfs) (by rw [e5]; exact hx15) (by rw [e6]; exact hdf))
      (fun s' h => Or.inl ⟨hc, h⟩)
  · refine ReachesRet.mono (xnAStep hRR hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC hl0e
      hx hxN hc hxl9 hxs hacc2 r3e0 r3e8 r3f0 hfbp hmB hMo hM1 hsl hcX hL0 hL1 hbA hbB hinv S' e1 e2 e3 e4
      (by rw [e6]; exact h14) (by rw [e7]; exact hfs) (by rw [e8]; exact hx15) (by rw [e9]; exact hdf)
      e10)
      (fun s' h => Or.inr ⟨by omega, h⟩)

end FvModexp.Amd64.W4Pro
