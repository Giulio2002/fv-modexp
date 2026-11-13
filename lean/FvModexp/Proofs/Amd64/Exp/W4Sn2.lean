import FvModexp.Proofs.Amd64.Exp.W4DivS
import FvModexp.Proofs.Amd64.Exp.W4SnK
import FvModexp.Proofs.Amd64.Exp.W4SncR
import FvModexp.Proofs.Amd64.Exp.W4SnP
import FvModexp.Proofs.Amd64.Exp.W4Sn2R

set_option autoImplicit false

/-!
# window-4 prologue (amd64): `sn2Step` — from the return of `nat.lsh` (`lshRet`, fn+0x54b) to the function's `RET`
(agent expmc s53; twin of `Arm64.W4Sn2`)

`toSn2` (spills of `zz`, setup) → `keeps_own`/`Ctx.keep` → `snCallR` (`q := stk.nat(2n)`, return fn+0x575) →
`keeps_sn`/`Ctx.keep`, `ZZ.keep`, `below_sn`, `held_sn`, `slot_sn` → `divStep`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- the post of `sn2Step` (memories: `M1` after the spills, `M2` at `sn2Ret`) -/
@[reducible] def Sn2Q (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M1 M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
    Keeps R L L g fs sp K st l0 [(rrp, 8 * (2 * n))] M M1 ∧ Keeps R L L2 g fs sp K st l0 [(rrp, 8 * (2 * n))] M1 M2 ∧
    b - stackNatCost (stLen M st) (2 * n) ≤ b2 ∧ stLen M2 st = stLen M st + StackNat.rnd (2 * n) ∧
    DivQ R b2 costD L2 g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv M2 s'

theorem sn2_in (sp : Nat) : ∀ q ∈ sn2Ws sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 := by
  intro q hq
  simp only [sn2Ws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem sn2_in' (sp : Nat) : ∀ q ∈ sn2Ws sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x3c0 ∧ q.1 ≤ q.2 := by
  intro q hq
  simp only [sn2Ws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (simp only; omega)

theorem sn2_kept (sp : Nat) : ∀ j, KeptJ j → Outside (sp + j) 8 (sn2Ws sp) := by
  intro j hj
  simp only [KeptJ] at hj
  simp only [sn2Ws, outside_cons, outside_nil, and_true]
  omega

theorem sn2_slot {sp : Nat} {M M1 : Memory} (hF : MemFrame M M1 (sn2Ws sp)) (j : Nat)
    (hj : 0xa8 ≤ j ∧ j + 8 ≤ 0x188 ∨ 0x190 ≤ j) : M1.readLE (sp + j) 8 = M.readLE (sp + j) 8 :=
  hF.readLE _ _ (by simp only [sn2Ws, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
/-- facts of the context used by `sn2Step` -/
theorem Ctx.misc {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) :
    n ≤ 128 ∧ K + 8 ≤ sp ∧ 41512 ≤ K ∧ l0 ≤ stLen M st ∧ 0 < stCap M st ∧
    AW sp K (stFree M st).1 (stFree M st).2 := by
  obtain ⟨-, hce, hK, -, -, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsok, -, hl0, hcap, -, -, -, huw, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact ⟨hn128, by have := hce.2.1; omega, hK, hl0, hcap, (free_of_up huw.symm hl0 hsok.2.2.2.2.2.1).symm⟩

/-- the new stack nat `q` lies above `l0` and below the new length -/
theorem q_in {st l0 n : Nat} {M1 M2 : Memory} (hl0 : l0 ≤ stLen M1 st)
    (hlen : stLen M2 st = stLen M1 st + StackNat.rnd (2 * n)) :
    stW M2 st + 8 * l0 ≤ stW M2 st + 8 * stLen M1 st ∧
      stW M2 st + 8 * stLen M1 st + 8 * (2 * n) ≤ stW M2 st + 8 * stLen M2 st := by
  have : 2 * n ≤ StackNat.rnd (2 * n) := by simp only [StackNat.rnd]; omega
  omega

/-- the new stack nat is a live nat of the stack's array -/
theorem q_live {R : RtInv} {L : List (Nat × Nat)} {st q n : Nat} {M : Memory} (hsok : StkOK M R L st)
    (hcap : 0 < stCap M st) (h1 : stW M st ≤ q) (h2 : q + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (h8 : (q - stW M st) % 8 = 0) : NatLive M R L q (2 * n) := by
  obtain ⟨-, -, -, -, hlive, hlc, -⟩ := hsok
  obtain ⟨a8, aH, aacc, a48⟩ := hlive hcap
  intro _
  exact ⟨by omega, held_sub aH h1 (by omega), M.accessible_sub aacc (Or.inr rfl) h1 (by omega), by omega⟩

theorem bud2 {x y b b2 : Nat} (h : x + y ≤ b) (h2 : b - x ≤ b2) : y ≤ b2 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sn2Step {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r t rrp zzp zzc : Nat} {M : Memory}
    (hKD : stkD ≤ K)
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [(rrp, 8 * (2 * n))] M)
    (hZ : ZZ R L g fs sp n mp xp yp ylen zp zc st zzp zzc M) (hzzK : AW sp K zzp (8 * zzc)) (hzl : 2 * n + 1 ≤ zzc)
    (hzv : M.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n)) (hzzr : Apart zzp (8 * zzc) rrp (8 * (2 * n)))
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrF : Apart rrp (8 * (2 * n)) (fs - 8) 8) (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (r190 : M.readLE (sp + 0x190) 8 = rrp) (ra8 : M.readLE (sp + 0xa8) 8 = 2 * n)
    (rd8 : M.readLE (sp + 0xd8) 8 = t) (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (ht : t < 2 ^ 64) (hfbp : fbp < 2 ^ 64)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl0 : stLen M st + 2 * n + 3 ≤ 2 ^ 16)
    (hsl1 : stLen M st + StackNat.rnd (2 * n) + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16)
    (hsl2 : stLen M st + StackNat.rnd (2 * n) + 17 * n + 3 ≤ 2 ^ 16)
    (hcF : costF (stLen M st + StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : stackNatCost (stLen M st) (2 * n) + (costD + (blockSize (8 * n) true +
      stackNatCost (stLen M st + StackNat.rnd (2 * n)) (17 * n) + 2 * blockSize (8 * (2 * n + 4)) true)) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 lshRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h3 : S.regs 3 = BitVec.ofNat 64 (2 * n + 1))
    (h1 : S.regs 1 = BitVec.ofNat 64 zzc)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (Sn2Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp t zzp zzc rrp Xv M) := by
  have hc0 : stackNatCost (stLen M st) (2 * n) ≤ b := Nat.le_trans (Nat.le_add_right _ _) hbud
  obtain ⟨hal, hsp1, hsp2, hacc, hacc2, r3d8, -, -, -, hstw, hrt, hst48, hn⟩ := Ctx.td hC
  obtain ⟨hn128, hK8, hK, hl0, hcap, huw⟩ := Ctx.misc hC
  have hst64 : st < 2 ^ 64 := by omega
  have hn2 : 0 < 2 * n := by omega
  have hk16 : 2 * n ≤ 2 ^ 16 := by omega
  have hK4 : 4192 ≤ K := by omega
  have hZ0 := hZ
  obtain ⟨⟨-, hzc40, -, hz48, -, -, -, -⟩, -, -, -, -, -, -, -, -⟩ := hZ0
  have hzzp : zzp < 2 ^ 64 := by omega
  have hzzc : zzc < 2 ^ 64 := by omega
  have hzzl : 2 * n + 1 < 2 ^ 64 := by omega
  refine toSn2 hal hsp1 hsp2 hacc hacc2 r3d8 r78 hzzp hzzl hzzc S hpc hsp hmem h0 h3 h1
    (fun S1 fpc fsp q0 q3 q5 q14 qfs qx qdf hF hreg w0 w188 wa0 w98 => ?_)
  -- the spills
  have hk1 := keeps_own hC hF hreg (sn2_in sp) (sn2_kept sp)
  have hC1 := Ctx.keep hC hk1
  have hacw : ∀ a k w, S1.mem.accessible a k w = M.accessible a k w := hk1.2.1
  obtain ⟨ew, el, ec⟩ := own_stkW hF (sn2_in sp) hstw
  have hZ1 := ZZ.keep hZ (LiveExt.refl R L) hacw (Or.inl ⟨ew, ec⟩)
  have hzv1 : S1.mem.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n) :=
    (own_rdW hF (sn2_in sp) (Apart.mono hzzK (zz_len hzl) (Nat.le_refl _))).trans hzv
  have hrB1 : (stW S1.mem st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW S1.mem st + 8 * stLen S1.mem st) ∨
      Apart rrp (8 * (2 * n)) (stW S1.mem st) (8 * stCap S1.mem st) := by
    rw [ew, el, ec]; exact hrB
  have hrL1 := natLive_acc hacw hrL
  have hinv1 := own_invW hF (sn2_in' sp) hK8 hrt hinv
  have hpre : SnPre R b L g fs sp st (2 * n) S1.mem :=
    snPre_of hC1 hserv hk16 (by rw [el]; exact hsl0) (by rw [el]; exact hc0) hinv1
  -- the call `q := stk.nat(2n)`
  refine snCallR hap hSN 0x575 (by decide) S1 hpre hst64 fpc fsp w0 q0 q3 q5 (q14.trans h14)
    (by rw [qfs]; exact hfs) (qx.trans hx15) (qdf.trans hdf)
    (fun S2 L2 b2 gpc gsp g5 g14 gfs gx gdf gX0 gX3 gX1 hS => ?_)
  have hk2 := keeps_sn hC1 hn2 hS
  have hC2 := Ctx.keep hC1 hk2
  have hS0 := hS
  obtain ⟨hx2, hb2, hinv2, hsok2, hlen2, -, -, hF2, -, -, -⟩ := hS0
  have hst2 := hk2.2.2.2.2.2.2.2.2.2.1
  have hZ2 := ZZ.keep hZ1 hx2 (fun a k w => hF2.accessible a k w) hst2
  obtain ⟨-, -, -, hl01, hcap1, huw1⟩ := Ctx.misc hC1
  have hsok1 := hk1.2.2.2.2.2.2.2.1
  have hlc1 := hsok1.2.2.2.2.2.1
  have hZ1' := hZ1
  obtain ⟨⟨-, -, -, -, hzH1, -, -, -⟩, -, -, -, -, -, hzS1, hzU1, -⟩ := hZ1'
  have hzv2 : S2.mem.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n) :=
    (held_sn hS (held_sub hzH1 (Nat.le_refl _) (Nat.add_le_add_left (zz_len hzl) _)) hK4
      (Apart.mono hzzK (zz_len hzl) (Nat.le_refl _)) (Apart.mono hzS1 (zz_len hzl) (Nat.le_refl _))
      (Apart.mono (arrFree hzU1 hlc1) (zz_len hzl) (Nat.le_refl _))).trans hzv1
  obtain ⟨hr8, hrH, hracc, hr48⟩ := hrL1 hn2
  obtain ⟨hrB2, hqr0⟩ := below_sn hS hrH hrB1
  have hrL2 : NatLive S2.mem R L2 rrp (2 * n) := fun _ =>
    ⟨hr8, hx2.held hrH, by rw [hF2.accessible]; exact hracc, hr48⟩
  have hcap2 : 0 < stCap S2.mem st := hk2.2.2.2.2.2.2.2.2.2.2.1 hcap1
  have hqin := q_in (M2 := S2.mem) hl01 hlen2
  have hqL : NatLive S2.mem R L2 (stW S2.mem st + 8 * stLen S1.mem st) (2 * n) :=
    q_live hsok2 hcap2 (Nat.le_add_right _ _) hqin.2 (by rw [Nat.add_sub_cancel_left]; exact Nat.mul_mod_right _ _)
  have sl : ∀ j, 16 ≤ j → j + 8 ≤ 0x3c0 → S2.mem.readLE (sp + j) 8 = S1.mem.readLE (sp + j) 8 :=
    fun j a c => slot_sn hS hrt hK4 hK8 hstw huw1 j a c
  have hlenM : stLen S2.mem st = stLen M st + StackNat.rnd (2 * n) := by rw [hlen2, el]
  rw [el] at hb2
  refine ReachesRet.mono (divStep hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hKD hC2 hZ2 hzzK hzl hzv2
    (norm_of_pow hzv2) hzzr hqin hqL hqr0.symm hrL2 hrW hrG hrF hrS hrB2
    ((sl 0x190 (by decide) (by decide)).trans ((sn2_slot hF 0x190 (Or.inr (Nat.le_refl _))).trans r190))
    ((sl 0xa8 (by decide) (by decide)).trans ((sn2_slot hF 0xa8 (Or.inl ⟨Nat.le_refl _, by decide⟩)).trans ra8))
    ((sl 0x188 (by decide) (by decide)).trans w188) ((sl 0x98 (by decide) (by decide)).trans w98)
    ((sl 0xa0 (by decide) (by decide)).trans wa0)
    ((sl 0xd8 (by decide) (by decide)).trans ((sn2_slot hF 0xd8 (Or.inl ⟨by decide, by decide⟩)).trans rd8))
    ((sl 0x78 (by decide) (by decide)).trans ((hk1.2.2.2.2.1 0x78 (by decide)).trans r78))
    ht hfbp hkk hmB hMo hM1 (by rw [hlenM]; exact hsl1) (by rw [hlenM]; exact hsl2) (by rw [hlenM]; exact hcF)
    (by rw [hlenM]; exact bud2 hbud hb2) hinv2 S2 gpc gsp rfl (gX0 hn2) gX3 gX1 g14 gfs gx gdf) (fun s' h => ?_)
  exact ⟨S1.mem, S2.mem, L2, b2, hk1, hk2, hb2, hlenM, h⟩

end FvModexp.Amd64.W4Pro
