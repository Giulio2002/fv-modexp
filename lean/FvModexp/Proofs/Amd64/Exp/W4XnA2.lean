import FvModexp.Proofs.Amd64.Exp.W4XnAP
import FvModexp.Proofs.Amd64.Exp.W4XnR2
import FvModexp.Proofs.Amd64.Exp.W4XnJ

set_option autoImplicit false

/-!
# window-4 prologue (amd64): path A from the return of `z2 := stk.nat(n)` (`aSn2Ret`) to the function's `RET`
(agent expmc s56; twin of `Arm64.W4XnA.xnA2K`)

`xnA2` (stack arguments `x`, `m`; registers `q`, `stk`, `z2`) → `nat.div` (`divCallG`, return fn+0x2d6) → `xnA3`
(`x := r`) → the join `xnJStep` at the stack level after the division, with `x`'s value `X % Mv`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- the post of `xnA2K` (`M` at `aSn2Ret`; `X` the value of the not yet normalised `x`) -/
@[reducible] def XnA2Q (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp qp k X : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M5 : Memory) (L5 : List (Nat × Nat)) (b5 : Nat),
    KeepsX R L L5 g fs sp K st l0 [(qp, 8 * k)] M M5 ∧ b - costD ≤ b5 ∧ stLen M5 st = stLen M st ∧
    XnJQ R b5 costD L5 g fs sp K n mp Mv yp ylen Y yi zp zc st n0 (stLen M st) fbp (X % Mv) M5 s'

theorem w1_in (sp : Nat) : ∀ q ∈ [(sp - 8, sp + 0x30)], sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 := by
  intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact ⟨Nat.le_refl _, by omega⟩

theorem w1_in' (sp : Nat) : ∀ q ∈ [(sp - 8, sp + 0x30)], sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2 := by
  intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact ⟨Nat.le_refl _, by omega, by omega⟩

theorem w1_kept (sp : Nat) : ∀ j, KeptJX j → Outside (sp + j) 8 [(sp - 8, sp + 0x30)] := by
  intro j hj; simp only [KeptJX] at hj; simp only [outside_cons, outside_nil, and_true]; omega

/-- the stack header is not in the argument stores' window -/
theorem hdr_w1 {M M' : Memory} {sp K st : Nat} (hF : MemFrame M M' [(sp - 8, sp + 0x30)]) (h : AW sp K st 24)
    (hK : K + 8 ≤ sp) : stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st := by
  simp only [AW, Apart] at h
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_⟩ <;>
    (simp only [outside_cons, outside_nil, and_true]; omega)

theorem natLive_accW {M M' : Memory} {R : RtInv} {L : List (Nat × Nat)} {p c : Nat}
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w) (h : NatLive M R L p c) : NatLive M' R L p c :=
  fun hc => by obtain ⟨a, b, d, e⟩ := h hc; exact ⟨a, b, by rw [hacc]; exact d, e⟩

theorem norm_keep {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 xp xl : Nat} {ex : List (Nat × Nat)} {M M' : Memory}
    (hob : ∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k)
    (hxO : Obj R L sp K st l0 ex M xp (8 * xl)) (h : NatNorm M xp xl) : NatNorm M' xp xl := by
  rcases Nat.eq_zero_or_pos xl with h0 | h0
  · exact Or.inl h0
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hob _ _ (obj_subk hxO (by omega) (by omega))]; exact h)

theorem ble {c x b b' : Nat} (h1 : c + x ≤ b) (h2 : b - c ≤ b') : x ≤ b' := by omega

theorem cle {c x b : Nat} (h1 : c + x ≤ b) : c ≤ b := by omega

set_option maxRecDepth 20000 in
theorem CtxX.ra {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) :
    mc < 2 ^ 40 ∧ M.readLE (sp + 0x3b8) 8 = mc ∧ (InRanges st 24 L ∨ Outside st 24 R.rt) ∧
      Apart st 24 (stUp M st l0).1 (stUp M st l0).2 ∧ StkOK M R L st ∧ 0 < stCap M st ∧
      AW sp K (stW M st) (8 * stCap M st) ∧ l0 ≤ stLen M st := by
  obtain ⟨-, -, -, -, -, -, -, hmc', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsth, -, hsok, -, hl0, hcap,
    harr, -, -, -, hsu, -, -, -, -, -, -, -, -, -, -, -, r3b8, -, -, -, -, -, -⟩ := h
  exact ⟨hmc', r3b8, hsth, hsu, hsok, hcap, (harr hcap).1, hl0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- path A from `aSn2Ret` to the function's `RET`: the division, `x := r`, the join -/
theorem xnA2K {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r qp k z2p xp xl xc : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : CtxX R L g fs sp K n mp mc Mv xp0 Xv0 yp ylen Y yi zp zc st n0 l0 fbp r [(qp, 8 * k)] M)
    (hlen : stLen M st = l0 + StackNat.rnd k + StackNat.rnd n)
    (hz2 : z2p = stW M st + 8 * (l0 + StackNat.rnd k))
    (hk0 : 0 < k) (hk40 : k < 2 ^ 40) (hqL : NatLive M R L qp k) (hqW : AW sp K qp (8 * k))
    (hqG : Apart qp (8 * k) (g + 16) 8) (hqF : Apart qp (8 * k) (fs - 8) 8) (hqS : Apart qp (8 * k) st 24)
    (hqB : (stW M st + 8 * l0 ≤ qp ∧ qp + 8 * k ≤ stW M st + 8 * stLen M st) ∨
      Apart qp (8 * k) (stW M st) (8 * stCap M st))
    (hqz : Apart qp (8 * k) z2p (8 * n))
    (hxO : Obj R L sp K st l0 [(qp, 8 * k)] M xp (8 * xl)) (hxa : M.accessible xp (8 * xl) false = true)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxN : NatNorm M xp xl) (hxl9 : xl ≤ 2 ^ 9) (hxc : xc < 2 ^ 64)
    (hacc2 : M.accessible (sp + 0x3c0) 0x38 false = true)
    (r3e0 : M.readLE (sp + 0x3e0) 8 = xp) (r3e8 : M.readLE (sp + 0x3e8) 8 = xl) (r3f0 : M.readLE (sp + 0x3f0) 8 = xc)
    (r370 : M.readLE (sp + 0x370) 8 = qp) (r140 : M.readLE (sp + 0x140) 8 = k) (r138 : M.readLE (sp + 0x138) 8 = k)
    (hfbp : fbp < 2 ^ 64) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl : stLen M st + 16 * xl + 64 ≤ 2 ^ 16) (hcX : costF (stLen M st) xl n ≤ costD)
    (hL0 : XjL costF n costD (stLen M st)) (hL1 : XjL costF n costD (stLen M st + StackNat.rnd n))
    (hb0 : costD + xjBud n costD (stLen M st) ≤ b)
    (hbud : costD + (stackNatCost (stLen M st) n + xjBud n costD (stLen M st + StackNat.rnd n)) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 aSn2Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 z2p) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XnA2Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp qp k (M.readLE xp (8 * xl)) M) := by
  obtain ⟨-, hsp1, hsp2, hacc, -, r3a8, -, hn, hn128, -, hm48, -, -, hst48, hstw, hrt, hK8⟩ := CtxX.xj hC
  obtain ⟨-, -, hsok, hcap, hl0, -, -, -, -, -, -, r3b0, -, -, r3d8⟩ := CtxX.nb hC
  obtain ⟨hmc, r3b8, -⟩ := CtxX.ra hC
  have hlc : stLen M st ≤ stCap M st := hsok.2.2.2.2.2.1
  obtain ⟨la8, -, -, la48⟩ := hsok.2.2.2.2.1 hcap
  have hq48 := (hqL hk0).2.2.2
  have hz64 : z2p < 2 ^ 64 := by rw [hz2]; omega
  have hz8 : z2p % 8 = 0 := by rw [hz2]; omega
  have hzin : stW M st + 8 * l0 ≤ z2p ∧ z2p + 8 * n ≤ stW M st + 8 * stLen M st := by
    rw [hz2, hlen]; simp only [StackNat.rnd]; omega
  have hcb := cle hb0
  refine xnA2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hxc hsp1 hsp2
    hacc hn128 hacc2 hz64 r3d8 r3b0 r3a8 r3b8 r3e0 r3e8 r3f0 r370 r140 r138 S hpc hsp hmem h0 h3 h1
    (fun S4 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 hmf hrg d17 w0 w1 w2 w3 w4 w5 => ?_)
  have hkw := keeps_ownX hC hmf hrg (w1_in sp) (w1_kept sp)
  have hCw := CtxX.keep hC hkw
  obtain ⟨eW, eL, eC⟩ := hdr_w1 hmf hstw hK8
  have haw : ∀ a k w, S4.mem.accessible a k w = M.accessible a k w := hkw.2.1
  have hinvw := inv_own hmf (w1_in' sp) hrt hK8 hinv
  have hxOw := obj_keepX hkw (by rw [eC]; omega) hxO
  have hzinw : stW S4.mem st + 8 * l0 ≤ z2p ∧ z2p + 8 * n ≤ stW S4.mem st + 8 * stLen S4.mem st := by
    rw [eW, eL]; exact hzin
  have xval : S4.mem.readLE xp (8 * xl) = M.readLE xp (8 * xl) := hkw.2.2.2.1 _ _ hxO
  have hpre := dvgPre_of (stkD := stkD) (b := b) (costF := costF) (costD := costD) (xc := xc) hCw hk40
    (natLive_accW haw hqL) hqW hqG hqF hqS (by rw [eW, eL, eC]; exact hqB) hqz hzinw hz8 hxOw
    (by rw [haw]; exact hxa) hx48 (norm_keep hkw.2.2.2.1 hxO hxN) hxl9 hKD hserv w0 w1 w2 w3 w4 w5
    (by rw [eL]; exact hsl) (by rw [eL]; exact hcX) hcb hinvw
  refine divCallG hap hDiv hnsD hnsW 0x2d6 (by decide) S4 hpre (by omega) (by omega) hz64 d1 d2 (by rw [d17])
    d3 d4 d5 d6 d7 d8 d9 d10 (by rw [d11, h14]) (by rw [d12, hfs]) (by rw [d13, hx15]) (by rw [d14, hdf])
    (fun S5 L5 b5 r' rl rc e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hD => ?_)
  have hk5 := keeps_divX hCw hKD hzinw (by rw [haw]; exact (hqL hk0).2.2.1) hqW hqG hqF hD
  have hC5 := CtxX.keep hCw hk5
  obtain ⟨-, -, hsthw, hsuw, hsokw, hcapw, harrw, -⟩ := CtxX.ra hCw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hmvw, -, -, -, -, -⟩ := CtxX.xj hCw
  have hcap5 : 0 < stCap S5.mem st := hk5.2.2.2.2.2.2.2.2.2.2.1 hcapw
  have hlen5 : stLen S5.mem st = stLen S4.mem st := hD.2.2.2.2.1.1.2.1
  obtain ⟨hxi, hval, hrln, hr64⟩ := rem_xin hrt hsthw hsuw hsokw hcapw harrw hzinw hn hmvw hmB (by omega) hD hcap5
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, q3b0, q3c0, q3d0, q3d8⟩ := CtxX.nb hC5
  have hacc5 : ∀ a k w, S5.mem.accessible a k w = M.accessible a k w := fun a k w => by rw [hk5.2.1, haw]
  refine xnA3 hsp1 hsp2 (by rw [hacc5]; exact hacc) (by rw [hacc5]; exact hacc2) q3d8 q3b0 q3c0 q3d0 S5
    (by rw [e1]) e2 rfl (fun S6 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 => ?_)
  have hl0M : l0 ≤ stLen M st := by rw [hlen]; omega
  have hC6 := CtxX.raise (CtxX.dropEx hC5) (l1 := stLen M st) hl0M (by rw [hlen5, eL]; exact Nat.le_refl _)
  have hxi' : XIn R L5 sp K st (stLen M st) S5.mem r' rl rc := by rw [hlen5, eL] at hxi; exact hxi
  have hb5 : b - costD ≤ b5 := hD.2.2.1
  refine ReachesRet.mono (xnJStep hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC6
    (by rw [hlen5, eL]) hxi' hrln (by have := hxi.2.2.1; omega) hfbp hmB hMo hM1 hL0 hL1 (ble hb0 hb5)
    (ble hbud hb5) hD.2.2.2.1 S6 g1 g3 g2 (g4.trans e8) (g5.trans e9) (g6.trans e10) g8 g7 (g10.trans e4)
    (by rw [g11]; exact e5) (by rw [g12]; exact e6) (by rw [g13]; exact e7))
    (fun s' h => ⟨S5.mem, L5, b5, hkw.trans hk5 (by rw [eC]; omega), hb5, by rw [hlen5, eL], ?_⟩)
  rw [hval, xval] at h
  exact h

end FvModexp.Amd64.W4Pro
