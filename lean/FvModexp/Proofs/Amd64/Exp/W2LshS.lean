import FvModexp.Proofs.Amd64.Exp.W2LshK
import FvModexp.Proofs.Amd64.Exp.W2LshR
import FvModexp.Proofs.Amd64.Exp.W2Sn2

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `lshStep` — from the return of `stk.nat(2n)` #1 (`sn1Ret`, fn+0x525) to the
function's `RET` (agent expmc s54; twin of `Arm64.W2LshS`)

`toLsh` (`RR[0] = 1`, spills, setup) → `keeps_own2`/`Ctx.keep` → `lshCall` (`zz = 2^(128 n)`, fresh) →
`keeps_lsh`/`Ctx.keep`, `zz_of_lsh` → `sn2Step`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- the post of `lshStep` (memories: `M1` after `toLsh`, `M2` at `lshRet`) -/
@[reducible] def LshQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t rrp Xv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M1 M2 : Memory) (L2 : List (Nat × Nat)) (b2 zzp zzc : Nat),
    Keeps R L L g fs sp K st l0 [(rrp, 8 * (2 * n))] M M1 ∧ Keeps R L L2 g fs sp K st l0 [(rrp, 8 * (2 * n))] M1 M2 ∧
    b - makeCost (1 + 128 * n / 64 + 1) ≤ b2 ∧ stLen M2 st = stLen M st ∧
    2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L ∧
    Sn2Q R b2 costD L2 g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv M2 s'

theorem lsh_in (sp : Nat) :
    ∀ q ∈ [(sp - 8, sp), (sp + 0xa8, sp + 0xb0), (sp + 0x198, sp + 0x1a0)], sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x2a8 := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem lsh_kept (sp : Nat) :
    ∀ j, KeptJ j → Outside (sp + j) 8 [(sp - 8, sp), (sp + 0xa8, sp + 0xb0), (sp + 0x198, sp + 0x1a0)] := by
  intro j hj
  simp only [KeptJ] at hj
  simp only [outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 20000 in
/-- the frame slots above lsh's spill area survive the call -/
theorem slot_lsh {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp stkL rrp n p l c K : Nat} {M M' : Memory}
    (hD : LsPost R b L L' b' g sp stkL rrp n M M' p l c) (hrt : Outside (sp - 8 - K) (K + 688) R.rt)
    (hK : K + 8 ≤ sp) (hKL : stkL ≤ K) (j : Nat) (h1 : 56 ≤ j) (h2 : j + 8 ≤ 0x2a8) :
    M'.readLE (sp + j) 8 = M.readLE (sp + j) 8 := by
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hD
  refine hF.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega

/-- the invariant survives `toLsh`'s stores -/
theorem lsh_inv {R : RtInv} {b g sp K rrp n : Nat} {L : List (Nat × Nat)} {M M1 : Memory}
    (hF : MemFrame M M1 (lshWs sp rrp)) (hrt : Outside (sp - 8 - K) (K + 688) R.rt) (hK : K + 8 ≤ sp)
    (hrH : Held R L rrp (8 * (2 * n))) (hn : 0 < n)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L M1) := by
  refine FvModexp.Expmc.inv_frame hF (fun q hq => ?_) h
  simp only [lshWs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))
  · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))
  · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))
  · exact hrH.imp (fun h => h.sub (by simp only; omega) (by simp only; omega))
      (fun h => h.of_sub (by simp only; omega) (by simp only; omega))

theorem bud3 {x y b : Nat} (h : x + y ≤ b) : x ≤ b := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem lshStep {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsWL : nsL.contains W2Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r t rrp : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [(rrp, 8 * (2 * n))] M)
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrF : Apart rrp (8 * (2 * n)) (fs - 8) 8) (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (rd8 : M.readLE (sp + 0xd8) 8 = t) (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (ht : t < 2 ^ 64) (hfbp : fbp < 2 ^ 64)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl0 : stLen M st + 2 * n + 3 ≤ 2 ^ 16)
    (hsl1 : stLen M st + StackNat.rnd (2 * n) + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16)
    (hsl2 : stLen M st + StackNat.rnd (2 * n) + 5 * n + 3 ≤ 2 ^ 16)
    (hcF : costF (stLen M st + StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (stLen M st) (2 * n) + (costD + (blockSize (8 * n) true +
      stackNatCost (stLen M st + StackNat.rnd (2 * n)) (5 * n) + 2 * blockSize (8 * (2 * n + 4)) true))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 sn1Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 rrp) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (LshQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t rrp Xv M) := by
  obtain ⟨hal, hsp1, hsp2, hacc, -, -, -, r3b0, -, -, hrt, -, hn⟩ := Ctx.td hC
  obtain ⟨hn128, hK8, hK, -, -, -⟩ := Ctx.misc hC
  have hn2 : 0 < 2 * n := by omega
  obtain ⟨hr8, hrH, hracc, hr48⟩ := hrL hn2
  have hrW' := hrW
  simp only [AW, Apart] at hrW'
  refine toLsh hal hsp1 hsp2 hacc hn hn128 r3b0 (M.accessible_sub hracc (Or.inr rfl) (Nat.le_refl _) (by omega))
    (by omega) (by omega) S hpc hsp hmem h0 h1
    (fun S1 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 hmf hrg q8 q190 qa8 q1 => ?_)
  -- own stores (two slots, the return address and `RR[0]`)
  obtain ⟨hk1, k0, k1, k2⟩ := keeps_own2 (ws := [(sp - 8, sp), (sp + 0xa8, sp + 0xb0), (sp + 0x198, sp + 0x1a0)])
    (p := rrp) hC hmf hrg (lsh_in sp) (lsh_kept sp)
    (fun a k ho => (ho.2.2.2.2 _ (List.mem_singleton_self _)).mono (Nat.le_refl _) (by omega))
    (Apart.mono hrW (by omega) (Nat.le_refl _)) (Apart.mono hrG (by omega) (Nat.le_refl _))
    (Apart.mono hrF (by omega) (Nat.le_refl _)) (Apart.mono hrS (by omega) (Nat.le_refl _))
    (M.accessible_sub hracc (Or.inr rfl) (Nat.le_refl _) (by omega))
  have hC1 := Ctx.keep hC hk1
  have hinv1 := lsh_inv hmf hrt hK8 hrH hn hinv
  have hpre : LsPre R b L g fs sp K stkL rrp n S1.mem := by
    refine ⟨hC1.2.1, hKL, hserv, hn128, hn, ?_, by omega,
      hrH.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)),
      Apart.mono hrW (by omega) (Nat.le_refl _), bud3 hbud, hinv1⟩
    rw [hmf.accessible]; exact M.accessible_sub hracc (Or.inl rfl) (Nat.le_refl _) (by omega)
  refine lshCall hap hLsh hnsL hnsWL S1 hpre (by omega) e1 e2 q8 e3 e4 e5 e6 e7 e8 e9 e10
    (e11.trans h14) (by rw [e12]; exact hfs) (e13.trans hx15) (e14.trans hdf)
    (fun S2 L2 b2 p l c f1 f2 f3 f4 f5 f6 f7 g0 g3 g1 hD => ?_)
  obtain ⟨hk2, e0', e1', e2'⟩ := keeps_lsh hC1 hKL hD
  have hC2 := Ctx.keep hC1 hk2
  obtain ⟨hl, hZ, hzzK, hzl, hzv, hzzr, -, hzin, hzap⟩ := zz_of_lsh hC1 hrH q1 e0' e2' hD
  have hD0 := hD
  obtain ⟨-, -, hx2, hb2, hinv2, hF2, -, -⟩ := hD0
  have hrL2 : NatLive S2.mem R L2 rrp (2 * n) := fun _ =>
    ⟨hr8, hx2.held hrH, by rw [hF2.accessible, hmf.accessible]; exact hracc, hr48⟩
  have hrB2 : (stW S2.mem st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW S2.mem st + 8 * stLen S2.mem st) ∨
      Apart rrp (8 * (2 * n)) (stW S2.mem st) (8 * stCap S2.mem st) := by
    rw [e0', e1', e2', k0, k1, k2]; exact hrB
  have sl := fun j h1 h2 => slot_lsh (j := j) hD hrt hK8 hKL h1 h2
  have hlenE : stLen S2.mem st = stLen M st := by rw [e1', k1]
  refine ReachesRet.mono (sn2Step hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hKD hC2 hZ hzzK hzl hzv hzzr
    hrL2 hrW hrG hrF hrS hrB2
    ((sl 0x198 (by decide) (by decide)).trans q190) ((sl 0xa8 (by decide) (by decide)).trans qa8)
    ((hk2.2.2.2.2.1 0xd8 (by decide)).trans ((hk1.2.2.2.2.1 0xd8 (by decide)).trans rd8))
    ((hk2.2.2.2.2.1 0x78 (by decide)).trans ((hk1.2.2.2.2.1 0x78 (by decide)).trans r78))
    ht hfbp hkk hmB hMo hM1 (by rw [hlenE]; exact hsl0) (by rw [hlenE]; exact hsl1) (by rw [hlenE]; exact hsl2)
    (by rw [hlenE]; exact hcF) (by rw [hlenE]; exact bud2 hbud hb2) hinv2
    S2 f1 f2 rfl g0 (by rw [g3, hl]) g1 f4 f5 f6 f7) (fun s' h => ?_)
  exact ⟨S1.mem, S2.mem, L2, b2, p, c, hk1, hk2, hb2, hlenE, hzl, hzin, hzap, h⟩

end FvModexp.Amd64.W2Pro
