import FvModexp.Proofs.Amd64.Exp.W2CtxX
import FvModexp.Proofs.Amd64.Exp.W2XjR
import FvModexp.Proofs.Amd64.Exp.W2Sn1R
import FvModexp.Proofs.Amd64.Exp.W2Sn1

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `xjStep` — from the `x` join `xJ` (fn+0x426) to the function's `RET`
(agent expmc s54; twin of `Arm64.W2Xj`)

`toK` (`len(y)`, `len(m)` tests, `m[0]`) + `kLoop` (`k0` Newton loop) + `toSn1` (spills of the normalised `x`, `n`,
`t`, `2n`) + `sn1Step`; the context `Ctx` is assembled at the `stk.nat(2n)` call from `CtxX` (moved through the spills by
`keeps_ownX`) and the two spilled slots (`Ctx.ofX`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

theorem B_pos : 0 < Exp.B := by unfold Exp.B; exact Nat.two_pow_pos 64

theorem newtonLoop_lt (n0 : Nat) : ∀ (fuel j t k : Nat), n0 - 2 ^ j ≤ fuel → k < Exp.B →
    Exp.newtonLoop n0 j t k < Exp.B
  | 0, j, t, k, hf, hk => by
    rw [Exp.newtonLoop]; split
    · omega
    · exact hk
  | fuel + 1, j, t, k, hf, hk => by
    rw [Exp.newtonLoop]; split
    · have : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      have := Nat.two_pow_pos j
      exact newtonLoop_lt n0 fuel (j + 1) _ _ (by omega) (Nat.mod_lt _ B_pos)
    · exact hk

theorem newton_lt (m0 : Nat) : Exp.newton 64 m0 < Exp.B :=
  newtonLoop_lt 64 64 0 _ _ (by simp) (Nat.mod_lt _ B_pos)

/-- the stored `k0` word -/
theorem hkk_of {Mv : Nat} (ho : Mv % 2 = 1) :
    ((2 ^ 64 - Exp.newton 64 (Mv % Exp.B)) % 2 ^ 64 * Mv + 1) % Exp.B = 0 := by
  have hB : Exp.B = 2 ^ 64 := by unfold Exp.B; rfl
  have h1 : (Mv % Exp.B) % 2 = 1 := by rw [hB]; omega
  have h2 := Exp.montK0_spec (Mv % Exp.B) h1 (Nat.mod_lt _ B_pos)
  have hlt := newton_lt (Mv % Exp.B)
  unfold Exp.montK0 at h2
  obtain ⟨t, ht⟩ : ∃ t, Exp.newton 64 (Mv % Exp.B) = t := ⟨_, rfl⟩
  rw [ht] at h2 hlt ⊢
  rw [Nat.mod_eq_of_lt hlt] at h2
  rw [← hB]
  obtain ⟨q, hq⟩ : ∃ q, Mv = Mv % Exp.B + Exp.B * q := ⟨Mv / Exp.B, (Nat.mod_add_div Mv Exp.B).symm⟩
  rw [hq, Nat.mul_add, Nat.add_right_comm, Nat.mul_left_comm, Nat.add_mul_mod_self_left]
  exact h2

/-- the low limb of a value read from memory -/
theorem low_limb {M : Memory} {mp n Mv : Nat} (hn : 0 < n) (hmV : M.readLE mp (8 * n) = Mv) :
    M.readLE mp 8 = Mv % Exp.B := by
  have e := Janus.Arm64.Memory.readLE_add M mp 8 (8 * (n - 1))
  rw [show 8 + 8 * (n - 1) = 8 * n by omega, hmV] at e
  have hl := Janus.Arm64.Memory.readLE_lt M mp 8
  have hB64 : Exp.B = 256 ^ 8 := by unfold Exp.B; rfl
  rw [hB64, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- the facts of `CtxX` the run pieces use -/
theorem CtxX.xj {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) :
    sp % 16 = 0 ∧ 4296 ≤ sp ∧ sp + 0x2a8 ≤ 2 ^ 48 ∧ M.accessible (sp - 4296) (4296 + 0x2a8) true = true ∧
    M.readLE (sp + 0x280) 8 = ylen ∧ M.readLE (sp + 0x290) 8 = mp ∧ 0 < ylen ∧ 0 < n ∧ n ≤ 128 ∧
    M.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧ M.readLE mp (8 * n) = Mv ∧
    xp + 8 * n ≤ 2 ^ 48 ∧ st + 24 ≤ 2 ^ 48 ∧ AW sp K st 24 ∧ Outside (sp - 8 - K) (K + 688) R.rt ∧ K + 8 ≤ sp := by
  obtain ⟨he, hce, -, -, hn, hn128, -, -, hm, -, hmv, -, hx, -, -, -, -, -, -, -, hyl, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, r3a8, -, -, -, -, r398, -, -, -⟩ := h
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, r398, r3a8, hyl, hn, hn128, hm.1, hm.2.1, hmv, hx.2.1, hsok.2.2.2.1,
    hstw, hce.2.2.2.2.2.2.2.1, by have := hce.2.1; omega⟩

theorem sn1_in' (sp : Nat) : ∀ q ∈ sn1Ws sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x2a8 ∧ q.1 ≤ q.2 := by
  intro q hq
  simp only [sn1Ws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> (simp only; omega)

theorem sn1_in (sp : Nat) : ∀ q ∈ sn1Ws sp, sp - 8 ≤ q.1 ∧ q.2 ≤ sp + 0x2a8 := by
  intro q hq
  simp only [sn1Ws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> (simp only; omega)

theorem sn1_kept (sp : Nat) : ∀ j, KeptJX j → Outside (sp + j) 8 (sn1Ws sp) := by
  intro j hj
  simp only [KeptJX] at hj
  simp only [sn1Ws, outside_cons, outside_nil, and_true]
  omega

/-- the invariant survives `toSn1`'s stores -/
theorem sn1_inv {R : RtInv} {b g sp K : Nat} {L : List (Nat × Nat)} {M M1 : Memory}
    (hF : MemFrame M M1 (sn1Ws sp)) (hrt : Outside (sp - 8 - K) (K + 688) R.rt) (hK : K + 8 ≤ sp)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L M1) := by
  refine FvModexp.Expmc.inv_frame hF (fun q hq => Or.inr ?_) h
  have := sn1_in' sp q hq
  exact hrt.of_sub (by omega) (by omega)

/-- the post of `xjStep` (`M1` after `toSn1`'s spills) -/
@[reducible] def XjQ (R : RtInv) (b costD : Nat) (L : List (Nat × Nat))
    (g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp Xv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ M1 : Memory, KeepsX R L L g fs sp K st l0 [] M M1 ∧ stLen M1 st = stLen M st ∧
    Sn1Q R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp (Exp.newton 64 (Mv % Exp.B)) Xv M1 s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xjStep {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {g fs sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {M : Memory}
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [] M) (hl0e : stLen M st = l0)
    (hxc : xc < 2 ^ 64) (hfbp : fbp < 2 ^ 64)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hsl0 : l0 + StackNat.rnd (2 * n) + 2 * n + 3 ≤ 2 ^ 16)
    (hsl1 : l0 + 2 * StackNat.rnd (2 * n) + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16)
    (hsl2 : l0 + 2 * StackNat.rnd (2 * n) + 5 * n + 3 ≤ 2 ^ 16)
    (hcF : costF (l0 + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : stackNatCost l0 (2 * n) + (makeCost (1 + 128 * n / 64 + 1) +
      (stackNatCost (l0 + StackNat.rnd (2 * n)) (2 * n) + (costD + (blockSize (8 * n) true +
      stackNatCost (l0 + 2 * StackNat.rnd (2 * n)) (5 * n) + 2 * blockSize (8 * (2 * n + 4)) true)))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XjQ R b costD L g fs sp K n mp Mv yp ylen Y yi zp zc st n0 l0 fbp Xv M) := by
  obtain ⟨hal, hsp1, hsp2, hacc, r398, r3a8, hyl, hn, hn128, hma, hm48, hmV, hx48, hst48, hstw, hrt, hK8⟩ :=
    CtxX.xj hC
  have hm0 := low_limb hn hmV
  refine toK hsp1 hsp2 hacc (M.accessible_sub hma (Or.inl rfl) (Nat.le_refl _) (by omega))
    (by omega) r398 r3a8 hyl hn (by omega) hm0 S hpc hsp hmem h3 hdf
    (fun S1 k1 k2 k3 k4 k5 k6 k7 k8 k9 => ?_)
  have hBl : Exp.B = 18446744073709551616 := Exp.B_eq
  refine kLoop 6 0 _ _ sp S1 (by omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) k1
    (by rw [k9 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp]) hsp1 hsp2
    (by rw [k2]; exact hacc) k3 k4 k5 k8
    (fun S2 a1 a2 a3 a4 a5 a6 a7 => ?_)
  have ht : Exp.newtonLoop 64 0 ((Mv % Exp.B + 18446744073709551616 - 1) % 18446744073709551616)
      ((2 + 18446744073709551616 - Mv % Exp.B % 18446744073709551616) % 18446744073709551616) =
      Exp.newton 64 (Mv % Exp.B) := by
    unfold Exp.newton; rw [hBl]
  rw [ht] at a3
  have htl : Exp.newton 64 (Mv % Exp.B) < 2 ^ 64 := Nat.lt_of_lt_of_eq (newton_lt _) (by unfold Exp.B; rfl)
  have rg : ∀ i, i ≠ 2 → i ≠ 10 → i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 15 → S2.regs i = S.regs i :=
    fun i b1 b2 b3 b4 b5 b6 => (a7 i b3 b4 b5 b6).trans (k9 i b1 b2 b3 b4 b5 b6)
  refine toSn1 (M := M) (sp := sp) (n := n) (st := st) (xp := xp) (xc := xc) (t := Exp.newton 64 (Mv % Exp.B)) hal hsp1 hsp2 hacc hn128 (by omega) (by omega) hxc htl S2 a1
    (by rw [rg 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp]) (by rw [a2, k2])
    (by rw [rg 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h9])
    (by rw [rg 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h8])
    (by rw [rg 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]) a3
    (by rw [rg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3])
    (by rw [rg 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7])
    (fun S3 c1 c2 c3 c4 c5 c6 c7 c8 c9 hmf hrg q8 q78 qd8 q138 q140 q370 => ?_)
  -- the spills keep the context
  have hk := keeps_ownX hC hmf hrg (sn1_in sp) (sn1_kept sp)
  have hC1 := Ctx.ofX (CtxX.keep hC hk) q370 q138
  have hlen1 : stLen S3.mem st = stLen M st := by
    simp only [AW, Apart] at hstw
    exact hmf.readLE _ _ (outside_ws_of_win (lo := sp - 8) (hi := sp + 0x2a8) (by omega) (sn1_in sp))
  have hinv1 := sn1_inv hmf hrt hK8 hinv
  refine ReachesRet.mono (sn1Step hap hclr hmv hmk hwt hro hSN hserv hDiv hnsD hnsW hLsh hnsL hnsWL hKD hKL hC1
    (by rw [hlen1, hl0e]) qd8 q78 htl hfbp (hkk_of hMo) hmB hMo hM1 hsl0 hsl1 hsl2 hcF hbud hinv1
    S3 c1 c2 rfl q8 c3 c4
    (by rw [c6, rg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h14])
    (by rw [c7, a5, k7]; exact hfs) (by rw [c8, a4, k6]; exact hx15) (by rw [c9]; exact a6))
    (fun s' h => ⟨S3.mem, hk, hlen1, h⟩)

end FvModexp.Amd64.W2Pro
