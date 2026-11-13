import FvModexp.Proofs.Amd64.Exp.W2LshS

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `sn1Step` — from the entry of `RR := stk.nat(2n)` (#1, return `sn1Ret` = fn+0x525) to
the function's `RET` (nat.go:1397; agent expmc s54; twin of `Arm64.W2Sn1`)

The context `Ctx` (no extra range, `l0` = the stack length here) holds at this call (the spills of `xp`/`n` to
0x258/0x138 happen before it, in `toSn1`); after it, `RR` (the new stack nat, at level `l0`) becomes the context's extra
range (`Ctx.addEx`), and `lshStep` finishes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- the post of `sn1Step` (`M2` at `sn1Ret`; `RR` at level `l0` of the stack) -/
@[reducible] def Sn1Q (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t Xv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
    Keeps R L L2 g fs sp K st l0 [] M M2 ∧ b - stackNatCost l0 (2 * n) ≤ b2 ∧
    stLen M2 st = l0 + StackNat.rnd (2 * n) ∧
    LshQ R b2 costD L2 g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t (stW M2 st + 8 * l0) Xv M2 s'

theorem rnd2 (n : Nat) : 2 * n ≤ StackNat.rnd (2 * n) := by simp only [StackNat.rnd]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sn1Step {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r t : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [] M) (hl0e : stLen M st = l0)
    (rd8 : M.readLE (sp + 0xd8) 8 = t) (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (ht : t < 2 ^ 64) (hfbp : fbp < 2 ^ 64)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl0 : l0 + StackNat.rnd (2 * n) + 2 * n + 3 ≤ 2 ^ 16)
    (hsl1 : l0 + 2 * StackNat.rnd (2 * n) + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16)
    (hsl2 : l0 + 2 * StackNat.rnd (2 * n) + 5 * n + 3 ≤ 2 ^ 16)
    (hcF : costF (l0 + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : stackNatCost l0 (2 * n) + (makeCost (1 + 128 * n / 64 + 1) +
      (stackNatCost (l0 + StackNat.rnd (2 * n)) (2 * n) + (costD + (blockSize (8 * n) true +
      stackNatCost (l0 + 2 * StackNat.rnd (2 * n)) (5 * n) + 2 * blockSize (8 * (2 * n + 4)) true)))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 snE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8)) (hmem : S.mem = M)
    (hrd : M.readLE (sp - 8) 8 = sn1Ret)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 (2 * n))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (Sn1Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t Xv M) := by
  subst hmem
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hst48, hn⟩ := Ctx.td hC
  obtain ⟨hn128, hK8, hK, -, -, -⟩ := Ctx.misc hC
  have hst64 : st < 2 ^ 64 := by omega
  have hn2 : 0 < 2 * n := by omega
  have hr2 := rnd2 n
  have hc0 : stackNatCost (stLen S.mem st) (2 * n) ≤ b := by rw [hl0e]; exact Nat.le_trans (Nat.le_add_right _ _) hbud
  have hpre : SnPre R b L g fs sp st (2 * n) S.mem :=
    snPre_of hC hserv (by omega) (by rw [hl0e]; omega) hc0 hinv
  refine snCallR hap hSN 0x525 (by decide) S hpre hst64 hpc hsp hrd h0 h3 rfl h14 hfs hx15 hdf
    (fun S2 L2 b2 gpc gsp g5 g14 gfs gx gdf gX0 gX3 gX1 hS => ?_)
  have hk := keeps_sn hC hn2 hS
  have hC2 := Ctx.keep hC hk
  have hS0 := hS
  obtain ⟨-, hb2, hinv2, hsok2, hlen2, -, -, -, -, -, -⟩ := hS0
  rw [hl0e] at hlen2 hb2
  have hlc2 := hsok2.2.2.2.2.2.1
  have hin : stW S2.mem st + 8 * l0 ≤ (stW S2.mem st + 8 * l0, 8 * (2 * n)).1 ∧
      (stW S2.mem st + 8 * l0, 8 * (2 * n)).1 + (stW S2.mem st + 8 * l0, 8 * (2 * n)).2 ≤
        stW S2.mem st + 8 * stCap S2.mem st := by
    simp only; omega
  have hC3 := Ctx.addEx hC2 hin
  have hC3' := hC2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hcap2, -, hug2, huf2, huw2, hsu2, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC3'
  have hrL : NatLive S2.mem R L2 (stW S2.mem st + 8 * l0) (2 * n) :=
    q_live hsok2 hcap2 (Nat.le_add_right _ _) (by omega) (by rw [Nat.add_sub_cancel_left]; exact Nat.mul_mod_right _ _)
  have hlenE : stLen S2.mem st = l0 + StackNat.rnd (2 * n) := hlen2
  have h2r : l0 + StackNat.rnd (2 * n) + StackNat.rnd (2 * n) = l0 + 2 * StackNat.rnd (2 * n) := by omega
  refine ReachesRet.mono (lshStep hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC3 hrL
    (in_stUp huw2.symm hin.1 hin.2).symm (in_stUp hug2.symm hin.1 hin.2).symm (in_stUp huf2.symm hin.1 hin.2).symm
    (in_stUp hsu2 hin.1 hin.2).symm (Or.inl ⟨Nat.le_refl _, by rw [hlenE]; omega⟩)
    ((hk.2.2.2.2.1 0xd8 (by decide)).trans rd8) ((hk.2.2.2.2.1 0x78 (by decide)).trans r78)
    ht hfbp hkk hmB hMo hM1 (by rw [hlenE]; omega) (by rw [hlenE, h2r]; exact hsl1) (by rw [hlenE, h2r]; exact hsl2)
    (by rw [hlenE, h2r]; exact hcF) (by rw [hlenE, h2r]; exact bud2 hbud hb2) hinv2
    S2 gpc gsp rfl (by rw [hl0e] at gX0; exact gX0 hn2) gX1 g14 gfs gx gdf) (fun s' h => ?_)
  exact ⟨S2.mem, L2, b2, hk, hb2, hlenE, h⟩

end FvModexp.Amd64.W2Pro
