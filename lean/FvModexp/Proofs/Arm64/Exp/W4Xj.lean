import FvModexp.Proofs.Arm64.Exp.W4XjR

/-!
# window-4 prologue (arm64): `xjStep` — from the `x` join `xJ` (fn+0x2e8) to the function's `RET`

`toK` + `kLoop` (`k0` Newton loop) + `toSn1` (spills of the normalised `x`, `k0`, `2n`) + `sn1Step`; the context `Ctx`
is assembled at the `stk.nat(2n)` call from `CtxB` (moved through the spills by `keeps_ownB`) and the `x` facts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the frame's own stores keep the context -/
theorem keeps_ownB {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hreg : M'.regions = M.regions)
    (hin : ∀ r ∈ ws, sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 1040)
    (hsl : ∀ j, (824 ≤ j ∧ j + 8 ≤ 896 ∨ 912 ≤ j ∧ j + 8 ≤ 1040) →
      Outside (sp + j) 8 ws) :
    KeepsB R L L g sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hin' : ∀ r ∈ ws, sp - K ≤ r.1 ∧ r.2 ≤ sp + 1040 := fun r hr => by have := hin r hr; omega
  have ow : ∀ a k, Apart a k (sp - K) (K + 1040) → Outside a k ws := fun a k h =>
    outside_ws_of_win (by unfold Apart at h; omega) hin'
  have hst : Apart st 24 (sp - K) (K + 1040) := hstw
  have e0 := hF.readLE st 8 (ow _ _ (hst.mono (by omega) (Nat.le_refl _)))
  have e1 := hF.readLE (st + 8) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have e2 := hF.readLE (st + 16) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have hsok' := stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w)
  refine keeps_ofB hce hK (LiveExt.refl R L) (FvModexp.Expmc.frame_widen_rt hF)
    (FvModexp.Expmc.liveFrame_of_frame (ws := ([] : List (Nat × Nat))) hF (fun a k hin2 _ => ?_)) hreg ?_ ?_ (fun a k ho => ⟨ow _ _ ho.2.1, trivial⟩)
    hsl (outside_ws_of_win (lo := sp + 8) (hi := sp + 1040) (by omega) hin)
    (outside_ws_of_win (lo := sp + 8) (hi := sp + 1040) (by omega) hin) hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _) (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
  · obtain ⟨r, hr, h1, h2⟩ := hin2
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this
    exact outside_ws_of_win (lo := sp - K) (hi := sp + 1040) (by omega) hin'
  · intro r hr hlt
    have := hin r hr
    exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)
  · exact outside_ws_of_win (by unfold Apart at hga; omega) hin'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xjStep (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M) (hl0e : stLen M st = l0)
    (hx : Inp R L sp n M xp) (hxO : Obj R L sp K st l0 [] M xp (8 * n)) (hxv : M.readLE xp (8 * n) = Xv)
    (hxc : xc < 2 ^ 64)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + 2 * StackNat.rnd (2 * n) + 17 * n + 68 ≤ 2 ^ 16)
    (hbud : stackNatCost l0 (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l0 + StackNat.rnd (2 * n)) (2 * n) +
      (costD + (blockSize (8 * n) true + stackNatCost (l0 + 2 * StackNat.rnd (2 * n)) (17 * n) +
        blockSize (8 * (2 * n + 4)) true)))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbA : bA + xjBudA n costD l0 ≤ b) (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xJ) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 n)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h8 : S.regs 8 = BitVec.ofNat 64 ylen) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibExp.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ zzp zzc : Nat, (2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L0) ∧
        DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv (Exp.newton 64 (Mv % Exp.B)) yp ylen Y yi
        zp zc st n0 zzp zzc (l0 + 2 * StackNat.rnd (2 * n)) r18 r29 s')) := by
  have hB0 := hB
  obtain ⟨-, hce, hK, -, hn, hn128, -, -, hm, -, hmV, -, -, -, -, -, -, hyl, hyl',
    -, -, -, -, -, hsok, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, r960⟩ := hB0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hst48 := hsok.2.2.2.1
  -- the low limb of `m`
  have hm0 : M.readLE mp 8 = Mv % Exp.B := by
    have e := M.readLE_add mp 8 (8 * (n - 1))
    rw [show 8 + 8 * (n - 1) = 8 * n by omega, hmV] at e
    have hl := M.readLE_lt mp 8
    have hB64 : Exp.B = 256 ^ 8 := by unfold Exp.B; rfl
    rw [hB64, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have hmB0 : Mv % Exp.B < 2 ^ 64 := Nat.lt_of_lt_of_eq (Nat.mod_lt Mv B_pos) (by unfold Exp.B; rfl)
  refine toK impl ret hret _ ylen mp n (Mv % Exp.B) M (by omega) (by omega) hn (by omega) (by have := hm.2.1; omega)
    (M.accessible_sub hm.1 (Or.inl rfl) (Nat.le_refl _) (by omega)) hm0 S hpc h8 h10 h11 hmem
    (fun S1 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 => ?_)
  have hBl : Exp.B = 18446744073709551616 := Exp.B_eq
  refine kLoop impl ret hret _ 6 0 _ _ S1 (by omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) k1 k4 k5 k6
    (fun S2 a1 a2 a3 a4 a5 => ?_)
  have ht : Exp.newtonLoop 64 0 ((Mv % Exp.B + 18446744073709551616 - 1) % 18446744073709551616)
      ((2 + 18446744073709551616 - Mv % Exp.B % 18446744073709551616) % 18446744073709551616) =
      Exp.newton 64 (Mv % Exp.B) := by
    unfold Exp.newton; rw [hBl]
  rw [ht] at a4
  have htl : Exp.newton 64 (Mv % Exp.B) < 2 ^ 64 := Nat.lt_of_lt_of_eq (newton_lt _) (by unfold Exp.B; rfl)
  refine toSn1 impl ret hret _ sp st xp xc n (Exp.newton 64 (Mv % Exp.B)) M hal (by omega) hA
    (M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) (by omega) (by have := hx.2.1; omega) hxc hn128 htl
    S2 a1 (by rw [a2, k2, hsp]) (by rw [a5 3 (by decide) (by decide) (by decide) (by decide), k7, h3])
    (by rw [a5 4 (by decide) (by decide) (by decide) (by decide), k8, h4])
    (by rw [a5 5 (by decide) (by decide) (by decide) (by decide), k9, h5])
    (by rw [a5 6 (by decide) (by decide) (by decide) (by decide), k10, h6])
    (by rw [a5 11 (by decide) (by decide) (by decide) (by decide), k11, h11]) a4 (by rw [a3, k3])
    (fun S3 M1 c1 c2 c3 c4 c5 c6 c7 c8 cm hmf hrg q904 q328 q320 q224 q128 => ?_)
  -- the spills keep the context
  have ws_in : ∀ r ∈ [(sp + 128, sp + 136), (sp + 224, sp + 232), (sp + 320, sp + 336), (sp + 904, sp + 912)],
      sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 1040 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (simp only; omega)
  have hk := keeps_ownB hB hmf hrg ws_in (fun j hj => by simp only [outside_cons, outside_nil, and_true]; omega)
  have hB1 := CtxB.keep hB hk
  have hAn1 := Anc.keepB hAn hk hl0A (by rw [← hl0e]; exact hsok.2.2.2.2.2.1) (fun e he => by simp at he)
    hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hxO' := hxO
  obtain ⟨-, hxW, -, -, -⟩ := hxO'
  simp only [AW, Apart] at hxW
  have hx1 : Inp R L sp n M1 xp := ⟨by rw [hmf.accessible]; exact hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
  have hl0' : l0 ≤ stCap M1 st := by
    have u1 := hk.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1; have u2 := hk.2.2.2.2.2.2.2.2.2.1
    simp only [stLen, stCap] at u1 u2 hl0e ⊢; omega
  have hxv1 : M1.readLE xp (8 * n) = Xv := by
    rw [hmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hxv
  have hC := Ctx.ofB hB1 hx1 (objB_keep hk hl0' hxO) hxv1 q904 q328 q320
  have hlen1 : stLen M1 st = l0 := by
    rw [← hl0e]; exact hmf.readLE _ _ (by
      have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [AW, Apart] at this; simp only [outside_cons, outside_nil, and_true]; omega)
  exact sn1Step impl hap R hclr hmv hmk hSN nsD stkD costD hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL hserv ret hret b L
    g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 (Exp.newton 64 (Mv % Exp.B)) M1 r18 r29 f29 hKD hKL hC hlen1 htl
    q224 q128 (hkk_of hMo) hmB hMo hM1 hslen hbud (FvModexp.Expmc.inv_frame hmf (fun r hr => Or.inr (by
      have := ws_in r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hrt.of_sub (by omega) (by omega))) hinv)
    L0 bA M0 hAn1 hbA hl0A
    S3 c1 c2 c3 c4 c5 (by rw [c6, a5 18 (by decide) (by decide) (by decide) (by decide), k12, h18])
    (by rw [c7, a5 28 (by decide) (by decide) (by decide) (by decide), k13, h28])
    (by rw [c8, a5 29 (by decide) (by decide) (by decide) (by decide), k14, h29]) cm

end FvModexp.Arm64.W4Pro
