import FvModexp.Proofs.Amd64.Exp.W2DivP
import FvModexp.Proofs.Amd64.Exp.W2DivM
import FvModexp.Proofs.Amd64.Exp.W2DivR
import FvModexp.Proofs.Amd64.Exp.W2Own

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `divStep` — from the return of `stk.nat(2n)` #2 (`sn2Ret`, fn+0x5af) to the function's `RET`
(agent expmc s53; twin of `Arm64.W2DivS`)

`toDiv` (argument stores, `[sp - 8, sp + 48)`) → `keeps_own` + `Ctx.keep` (context at the call) → `dvPre_of` →
`divCall` (`RR = 2^(128n) mod m` by `nat.div`) → `keeps_div` + `Ctx.keep`, `rem_div`, `ZZ.keep`, `slot_div` → `rrRetC`.
The facts outside the context (`zz`, `q`, `RR`, the stack header, the invariant) are carried over the argument stores by
`own_rd` (they are apart from the window).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- the post of `divStep` (memories: `Mw` at the call, `M'` at `divRet`) -/
@[reducible] def DivQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (Mw M' : Memory) (L' : List (Nat × Nat)) (b' rp rl rc : Nat) (M1 : Memory) (rrq rrc onep : Nat) (M2 : Memory)
    (L2 : List (Nat × Nat)) (b2 : Nat),
    Keeps R L L g fs sp K st l0 [(rrp, 8 * (2 * n))] M Mw ∧ Keeps R L L' g fs sp K st l0 [(rrp, 8 * (2 * n))] Mw M' ∧
    b - costD ≤ b' ∧ stLen M' st = stLen M st ∧ M'.readLE rp (8 * rl) = 2 ^ (128 * n) % Mv ∧
    RRPost R b' L' g sp n rp rl rc zzp zzc M' M1 rrq rrc ∧ OneChain R b' L' L2 b2 sp n st M1 M2 ∧
    RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (5 * n) st n0 onep fbp
      Mv Xv (2 ^ (128 * n) % Mv) M2 s' ∧
    (Apart zzp (8 * zzc) (stW M' st) (8 * stCap M' st) ∧ Held R L' zzp (8 * zzc))

theorem win1 (sp : Nat) : ∀ q ∈ [(sp - 8, sp + 48)], sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x2a8 := by
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  exact ⟨Nat.le_refl _, by omega⟩

theorem win1_kept (sp : Nat) : ∀ j, KeptJ j → Outside (sp + j) 8 [(sp - 8, sp + 48)] := by
  intro j hj
  simp only [KeptJ] at hj
  simp only [outside_cons, outside_nil, and_true]
  omega

/-- a read apart from the window is kept by the argument stores -/
theorem own_rd {sp K a k : Nat} {M Mw : Memory} (hF : MemFrame M Mw [(sp - 8, sp + 48)]) (h : AW sp K a k) :
    Mw.readLE a k = M.readLE a k := by
  refine hF.readLE a k ?_
  simp only [AW, Apart] at h
  simp only [outside_cons, outside_nil, and_true]
  omega

/-- a frame slot above the argument area is kept by the argument stores -/
theorem own_slot {sp : Nat} {M Mw : Memory} (hF : MemFrame M Mw [(sp - 8, sp + 48)]) (j : Nat) (hj : 48 ≤ j) :
    Mw.readLE (sp + j) 8 = M.readLE (sp + j) 8 :=
  hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

theorem own_stk {sp K st : Nat} {M Mw : Memory} (hF : MemFrame M Mw [(sp - 8, sp + 48)]) (h : AW sp K st 24) :
    stW Mw st = stW M st ∧ stLen Mw st = stLen M st ∧ stCap Mw st = stCap M st :=
  ⟨own_rd hF (Apart.sub h (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)),
    own_rd hF (Apart.sub h (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)),
    own_rd hF (Apart.sub h (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _))⟩

theorem own_inv {R : RtInv} {b g sp K : Nat} {L : List (Nat × Nat)} {M Mw : Memory}
    (hF : MemFrame M Mw [(sp - 8, sp + 48)]) (hrt : Outside (sp - 8 - K) (K + 688) R.rt)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L Mw) := by
  refine FvModexp.Expmc.inv_frame hF (fun q hq => ?_) h
  simp only [List.mem_singleton] at hq
  subst hq
  exact held_sub (Or.inr hrt) (by omega) (by omega)

theorem natLive_acc {R : RtInv} {L : List (Nat × Nat)} {p c : Nat} {M Mw : Memory}
    (hacc : ∀ a k w, Mw.accessible a k w = M.accessible a k w) (h : NatLive M R L p c) : NatLive Mw R L p c := by
  intro hc
  obtain ⟨h1, h2, h3, h4⟩ := h hc
  exact ⟨h1, h2, by rw [hacc]; exact h3, h4⟩

theorem natNorm_rd {M Mw : Memory} {p k : Nat} (e : Mw.readLE (p + 8 * (k - 1)) 8 = M.readLE (p + 8 * (k - 1)) 8)
    (h : NatNorm M p k) : NatNorm Mw p k := by
  unfold NatNorm at h ⊢; rw [e]; exact h

theorem bud_sub {a c b b' : Nat} (h : c + a ≤ b) (h' : b - c ≤ b') : a ≤ b' := by omega

set_option maxRecDepth 20000 in
/-- what `toDiv` needs from the context -/
theorem Ctx.td {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) :
    sp % 16 = 0 ∧ 4296 ≤ sp ∧ sp + 0x2a8 ≤ 2 ^ 48 ∧ M.accessible (sp - 4296) (4296 + 0x2a8) true = true ∧
    M.accessible (sp + 0x2a8) 0x20 false = true ∧ M.readLE (sp + 0x2c0) 8 = st ∧ M.readLE (sp + 0x290) 8 = mp ∧
    M.readLE (sp + 0x298) 8 = n ∧ M.readLE (sp + 0x2a0) 8 = mc ∧ AW sp K st 24 ∧
    Outside (sp - 8 - K) (K + 688) R.rt ∧ st + 24 ≤ 2 ^ 48 ∧ 0 < n := by
  obtain ⟨he, hce, -, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcacc, -, -, r3a8, r3b0, r3b8, -, -, -, -, r3d8, -, -, -⟩ := h
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, hcacc, r3d8, r3a8, r3b0, r3b8, hstw, hce.2.2.2.2.2.2.2.1,
    hsok.2.2.2.1, hn⟩

theorem lt64_of_live {M : Memory} {R : RtInv} {L : List (Nat × Nat)} {p n : Nat} (hn : 0 < n)
    (h : NatLive M R L p (2 * n)) : p < 2 ^ 64 := by
  have := (h (by omega)).2.2.2; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem divStep {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W2Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r t qp rrp zzp zzc : Nat} {M : Memory}
    (hKD : stkD ≤ K)
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [(rrp, 8 * (2 * n))] M)
    (hZ : ZZ R L g fs sp n mp xp yp ylen zp zc st zzp zzc M) (hzzK : AW sp K zzp (8 * zzc)) (hzl : 2 * n + 1 ≤ zzc)
    (hzv : M.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n)) (hzN : NatNorm M zzp (2 * n + 1))
    (hzzr : Apart zzp (8 * zzc) rrp (8 * (2 * n)))
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (hqL : NatLive M R L qp (2 * n)) (hqr : Apart qp (8 * (2 * n)) rrp (8 * (2 * n)))
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrF : Apart rrp (8 * (2 * n)) (fs - 8) 8) (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (r190 : M.readLE (sp + 0x198) 8 = rrp) (ra8 : M.readLE (sp + 0xa8) 8 = 2 * n)
    (r188 : M.readLE (sp + 0x190) 8 = zzp) (r98 : M.readLE (sp + 0x98) 8 = 2 * n + 1)
    (ra0 : M.readLE (sp + 0xa0) 8 = zzc) (rd8 : M.readLE (sp + 0xd8) 8 = t) (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (ht : t < 2 ^ 64) (hfbp : fbp < 2 ^ 64)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl1 : stLen M st + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16) (hsl2 : stLen M st + 5 * n + 3 ≤ 2 ^ 16)
    (hcF : costF (stLen M st) (2 * n + 1) n ≤ costD)
    (hbud : costD + (blockSize (8 * n) true + stackNatCost (stLen M st) (5 * n) + 2 * blockSize (8 * (2 * n + 4)) true)
      ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 sn2Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h3 : S.regs 3 = BitVec.ofNat 64 (2 * n))
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (DivQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv M) := by
  have hcb : costD ≤ b := Nat.le_trans (Nat.le_add_right _ _) hbud
  obtain ⟨hal, hsp1, hsp2, hacc, hacc2, r3d8, r3a8, r3b0, r3b8, hstw, hrt, hst48, hn⟩ := Ctx.td hC
  have hst64 : st < 2 ^ 64 := by omega
  have hqp := lt64_of_live hn hqL
  have hrrp := lt64_of_live hn hrL
  refine toDiv hal hsp1 hsp2 hacc hacc2 r3d8 r190 ra8 r188 r98 ra0 r3a8 r3b0 r3b8 S hpc hsp hmem
    (fun S1 fpc fsp q0 q3 q1 q7 q6 q8 q9 q5 q14 qfs qx qdf hF hreg w0 w1 w2 w3 w4 w5 w6 => ?_)
  -- the context at the call
  have hk1 := keeps_own hC hF hreg (win1 sp) (win1_kept sp)
  have hCw := Ctx.keep hC hk1
  have hacw : ∀ a k w, S1.mem.accessible a k w = M.accessible a k w := hk1.2.1
  obtain ⟨ew, el, ec⟩ := own_stk hF hstw
  have hZw := ZZ.keep hZ (LiveExt.refl R L) hacw (Or.inl ⟨ew, ec⟩)
  have hzvw : S1.mem.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n) :=
    (own_rd hF (Apart.mono hzzK (zz_len hzl) (Nat.le_refl _))).trans hzv
  have hzNw : NatNorm S1.mem zzp (2 * n + 1) :=
    natNorm_rd (own_rd hF (Apart.sub hzzK (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _))) hzN
  have hqinw : stW S1.mem st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW S1.mem st + 8 * stLen S1.mem st := by
    rw [ew, el]; exact hqin
  have hrBw : (stW S1.mem st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW S1.mem st + 8 * stLen S1.mem st) ∨
      Apart rrp (8 * (2 * n)) (stW S1.mem st) (8 * stCap S1.mem st) := by
    rw [ew, el, ec]; exact hrB
  have hqLw := natLive_acc hacw hqL
  have hrLw := natLive_acc hacw hrL
  have hpre : DvPre R b costF costD L g fs sp K stkD st qp rrp n zzp (2 * n + 1) zzc mp mc S1.mem :=
    dvPre_of hCw hZw hzzK hzl hzNw hzzr hqinw hqLw hqr hrLw hrW hrG hrF hrS hrBw hKD hserv w1 w2 w3 w4 w5 w6
      (by rw [el]; exact hsl1) (by rw [el]; exact hcF) hcb (own_inv hF hrt hinv)
  -- the division
  refine divCall hap hDiv hnsD hnsW S1 hpre hst64 hqp hrrp fpc fsp w0 (q0.trans h0) (q3.trans h3) (q1.trans h1)
    q7 q6 q8 q9 q5 (q14.trans h14) (by rw [qfs]; exact hfs) (qx.trans hx15) (qdf.trans hdf)
    (by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hx⟩ := hC.1; rw [hacw]; exact hx)
    (fun S2 L' b' rp rl rc f4 f0 f5 f14 ffs fx15 fdf f7 f6 f8 hD => ?_)
  have hD0 := hD
  obtain ⟨-, hxD, hb', hinv', ⟨⟨-, hlen', hst'⟩, -⟩, -, hF2, -, -⟩ := hD0
  have hk2 := keeps_div hCw hKD hqinw hrLw hrW hrG hrF hD
  have hC' := Ctx.keep hCw hk2
  obtain ⟨hrl0, hrln, hrc, -, hra, hr48, hrh, hrw, hrS', hrF', hzr, hzz', hval⟩ :=
    rem_div hCw hZw hzzK hKD hqinw hrLw hrW hrS hrBw hzzr hzl hzvw hMo hM1 hmB hD
  have hZ' := ZZ.keep hZw hxD (fun a k w => hF2.accessible a k w) hst'
  have sl : ∀ j, 104 ≤ j → j + 8 ≤ 0x2a8 → KeptJ j → S2.mem.readLE (sp + j) 8 = M.readLE (sp + j) 8 :=
    fun j h1 h2 hj => (slot_div hCw hqinw hrW hD j h1 h2).trans (hk1.2.2.2.2.1 j hj)
  have sl' : ∀ j, 104 ≤ j → j + 8 ≤ 0x2a8 → S2.mem.readLE (sp + j) 8 = M.readLE (sp + j) 8 :=
    fun j h1 h2 => (slot_div hCw hqinw hrW hD j h1 h2).trans (own_slot hF j (Nat.le_trans (by decide) h1))
  have hlen : stLen S2.mem st = stLen M st := hlen'.trans el
  refine ReachesRet.mono (rrRetC hap hclr hmv hmk hwt hro hSN hserv hC' hZ' ht hfbp
    ((sl 0xd8 (by decide) (by decide) (by decide)).trans rd8) ((sl 0x78 (by decide) (by decide) (by decide)).trans r78)
    ((sl' 0xa0 (by decide) (by decide)).trans ra0) ((sl' 0x190 (by decide) (by decide)).trans r188)
    hkk hmB (by rw [hlen]; exact hsl2) (by rw [hlen]; exact bud_sub hbud hb') hinv' hrl0 hrln hrc hra hr48 hrh hrw
    hrS' hrF' hzr (zz_mid S2.mem hzz' hrln) S2 f4 f0 rfl f7 f6 f8 f5 f14 ffs fx15 fdf) (fun s' h => ?_)
  obtain ⟨M1, rrq, rrc, onep, M2, L2, b2, p1, p2, p3⟩ := h
  rw [hval, hlen] at p3
  exact ⟨S1.mem, S2.mem, L', b', rp, rl, rc, M1, rrq, rrc, onep, M2, L2, b2, hk1, hk2, hb', hlen, hval, p1, p2, p3,
    hZ'.2.2.2.2.2.2.2.1, hZ'.1.2.2.2.2.1⟩

end FvModexp.Amd64.W2Pro
