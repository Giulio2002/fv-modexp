import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4LshK
import FvModexp.Proofs.Arm64.Exp.W4LshR
import FvModexp.Proofs.Arm64.Exp.W4Sn2

/-!
# window-4 prologue (arm64): `lshStep` — from the return of `stk.nat(2n)` #1 (`sn1Ret`, fn+0x394) to the function's `RET`

`toLsh` (`RR[0] = 1`, setup) + `lshCallK` (`zz = 2^(128 n)`, fresh) + `sn2Step`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
/-- the frame slots above lsh's spill area survive the call -/
theorem slot_lsh {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp stkL rrp n p l c K : Nat} {M M' : Memory}
    (hD : LsPost R b L L' b' g sp stkL rrp n M M' p l c) (hrt : Outside (sp - K) (K + 1040) R.rt) (hK : K ≤ sp)
    (hKL : stkL ≤ K) (j : Nat) (h1 : 64 ≤ j) (h2 : j + 8 ≤ 1040) : M'.readLE (sp + j) 8 = M.readLE (sp + j) 8 := by
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hD
  refine hF.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem lshStep (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg34.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t rrp : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [(rrp, 8 * (2 * n))] M)
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (ht : t < 2 ^ 64) (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : stLen M st + StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcF : costF (stLen M st + StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (stLen M st) (2 * n) + (costD + (blockSize (8 * n) true +
      stackNatCost (stLen M st + StackNat.rnd (2 * n)) (17 * n) + blockSize (8 * (2 * n + 4)) true))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbA : bA + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (stLen M st) (2 * n) + costD)) ≤ b)
    (hl0A : stLen M0 st ≤ l0) (hexA : ALoc R L0 st M0 (rrp, 8 * (2 * n)))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 sn1Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 rrp) (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ zzp zzc : Nat, (2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L0) ∧
        DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv t yp ylen Y yi zp zc st n0 zzp zzc
        (stLen M st + StackNat.rnd (2 * n)) r18 r29 s')) := by
  have hC0 := hC
  obtain ⟨-, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, r1024, -, -, -, -, -, -, -, -, -⟩ := hC0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hrL0 := hrL
  obtain ⟨hr8, hrH, hracc, hr48⟩ := hrL0 (by omega)
  have hrW' := hrW
  simp only [AW, Apart] at hrW'
  refine toLsh impl ret hret _ sp rrp n M hal (by omega) hA (M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega))
    hn hn128 r1024 (M.accessible_sub hracc (Or.inr rfl) (Nat.le_refl _) (by omega)) (by omega) (by omega)
    S hpc hsp h0 h2 hmem (fun S1 M1 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 em hmf hrg q176 q408 q1 => ?_)
  -- own stores (two slots and `RR[0]`)
  have ws_in : ∀ r ∈ [(sp + 176, sp + 184), (sp + 408, sp + 416)], sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 1040 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only; omega)
  obtain ⟨hk1, k0, k1, k2⟩ := keeps_own2 (ws := [(sp + 176, sp + 184), (sp + 408, sp + 416)]) (p := rrp) hC hmf hrg
    ws_in (fun j hj => by simp only [outside_cons, outside_nil, and_true]; omega)
    (fun a k ho => (ho.2.2.2.2 _ (List.mem_singleton_self _)).mono (Nat.le_refl _) (by omega))
    (Apart.mono hrW (by omega) (Nat.le_refl _)) (Apart.mono hrG (by omega) (Nat.le_refl _))
    (Apart.mono hrS (by omega) (Nat.le_refl _)) (M.accessible_sub hracc (Or.inr rfl) (Nat.le_refl _) (by omega))
  have hC1 := Ctx.keep hC hk1
  have hl0c : l0 ≤ stCap M st := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -, h1, -⟩ := hC
    exact Nat.le_trans h1 hs.2.2.2.2.2.1
  have hAn1 := Anc.keep hAn hk1 hl0A hl0c (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexA) hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hinv1 : R.inv b L g (view R.rt L M1) := by
    refine FvModexp.Expmc.inv_frame hmf (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inr (hrt.of_sub (by omega) (by omega))
    · exact Or.inr (hrt.of_sub (by omega) (by omega))
    · exact hrH.imp (fun h => h.sub (by simp only; omega) (by simp only; omega))
        (fun h => h.of_sub (by simp only; omega) (by simp only; omega))
  have hpre : LsPre R b L g sp K stkL rrp n M1 := by
    refine ⟨hC1.2.1, hKL, hserv, hn128, hn, ?_, by omega,
      hrH.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)),
      Apart.mono hrW (by omega) (Nat.le_refl _), by omega, hinv1⟩
    rw [hmf.accessible]; exact M.accessible_sub hracc (Or.inl rfl) (Nat.le_refl _) (by omega)
  refine lshCallK impl hap R nsL stkL hLsh hnsL hnsWL ret hret _ b L g sp K rrp n M1 r18 f29 hpre (by omega)
    S1 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 (e11.trans h18) (e12.trans h28) (e13.trans h29) em
    (fun S2 M2 L2 b2 p l c f1 f2 f3 f4 f5 f6 f7 f8 f9 hD => ?_)
  obtain ⟨hk2, e0', e1', e2'⟩ := keeps_lsh hC1 hKL hD
  have hC2 := Ctx.keep hC1 hk2
  have hAn2 := Anc.keep hAn1 hk2 hl0A (by rw [k2]; exact hl0c) (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexA) hC1.2.1.2.2.2.2.2.2.2.2.2.2.1 hK0
  obtain ⟨hl, hZ, hzzK, hzl, hzv, hzzr, hc40⟩ := zz_of_lsh hC1 hrH q1 e0' e2' hD
  have hD0 := hD
  obtain ⟨-, -, hx2, hb2, hinv2, hF2, -, -⟩ := hD0
  have hrL2 : NatLive M2 R L2 rrp (2 * n) := fun _ =>
    ⟨hr8, hx2.held hrH, by rw [hF2.accessible, hmf.accessible]; exact hracc, hr48⟩
  have hrB2 : (stW M2 st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M2 st + 8 * stLen M2 st) ∨
      Apart rrp (8 * (2 * n)) (stW M2 st) (8 * stCap M2 st) := by
    rw [e0', e1', e2', k0, k1, k2]; exact hrB
  have sl := fun j h1 h2 => slot_lsh (j := j) hD hrt hK0 hKL h1 h2
  have rs1 : ∀ j, (j + 8 ≤ 176 ∨ 184 ≤ j ∧ j + 8 ≤ 408 ∨ 416 ≤ j) → j + 8 ≤ 1040 →
      M1.readLE (sp + j) 8 = M.readLE (sp + j) 8 := fun j hj hj2 =>
    hmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hlenE : stLen M2 st = stLen M st := by rw [e1', k1]
  refine reaches_mono (sn2Step impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW hserv ret hret b2 L2 g sp K n
    mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t rrp p c M2 r18 r29 f29 hKD hC2 hZ hzzK hzl hzv hzzr hrL2 hrW hrG hrS
    hrB2 (by rw [sl 408 (by omega) (by omega)]; exact q408) (by rw [sl 176 (by omega) (by omega)]; exact q176) ht
    (by rw [sl 224 (by omega) (by omega), rs1 224 (by omega) (by omega)]; exact r224)
    (by rw [sl 128 (by omega) (by omega), rs1 128 (by omega) (by omega)]; exact r128)
    hkk hmB hMo hM1 (by rw [hlenE]; exact hslen) (by rw [hlenE]; exact hcF) (by rw [hlenE]; omega) hinv2
    L0 bA M0 hAn2 (by rw [hlenE]; exact ble2 hbA hb2) hl0A hexA
    S2 f1 f2 f3 (by rw [f4, hl]) f5 f6 f7 f8 f9)
    (isReturn_mono fun s' h => ⟨p, c, ⟨hzl, (hD.1.2.2.2.2.2.2 (Nat.succ_pos _) (Nat.lt_of_lt_of_le (Nat.succ_pos _) hzl)).1,
      apartAll_ext hAn.1 (hD.1.2.2.2.2.2.2 (Nat.succ_pos _) (Nat.lt_of_lt_of_le (Nat.succ_pos _) hzl)).2⟩, by rw [hlenE] at h; exact h⟩)

end FvModexp.Arm64.W4Pro
