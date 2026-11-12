import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2DivS
import FvModexp.Proofs.Arm64.Exp.W2Sn2K
import FvModexp.Proofs.Arm64.Exp.W2Sn2R
import FvModexp.Proofs.Arm64.Exp.W2SnK

/-!
# window-2 prologue (arm64): `sn2Step` — from the return of `nat.lsh` (`lshRet`, fn+0x3d8) to the function's `RET`

`toSn2` (spills of `zz`, setup) + `snCallK` (`q := stk.nat(2n)`) + `divStep`, the context moved by
`keeps_own`/`keeps_sn`/`Ctx.keep`, `ZZ.keep`, `below_sn`, `held_sn`, `slot_sn`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sn2Step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t rrp zzp zzc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K)
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [(rrp, 8 * (2 * n))] M)
    (hZ : ZZ R L g sp n mp xp yp ylen zp zc st l0 zzp zzc M) (hzzK : AW sp K zzp (8 * zzc)) (hzl : 2 * n + 1 ≤ zzc)
    (hzv : M.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n))
    (hzzr : Apart zzp (8 * zzc) rrp (8 * (2 * n)))
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (r408 : M.readLE (sp + 408) 8 = rrp) (r176 : M.readLE (sp + 176) 8 = 2 * n)
    (ht : t < 2 ^ 64) (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : stLen M st + StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcF : costF (stLen M st + StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : stackNatCost (stLen M st) (2 * n) + (costD + (blockSize (8 * n) true +
      stackNatCost (stLen M st + StackNat.rnd (2 * n)) (5 * n) + blockSize (8 * (2 * n + 4)) true)) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbA : bA + (stackNatCost (stLen M st) (2 * n) + costD) ≤ b) (hl0A : stLen M0 st ≤ l0)
    (hexA : ALoc R L0 st M0 (rrp, 8 * (2 * n)))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 lshRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n + 1))
    (h2 : S.regs 2 = BitVec.ofNat 64 zzc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv t yp ylen Y yi zp zc st n0 zzp zzc (stLen M st + StackNat.rnd (2 * n))
        r18 r29)) := by
  have hC0 := hC
  obtain ⟨-, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, r672, -, -, -⟩ := hC0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hZ0 := hZ
  obtain ⟨⟨-, hzc40, -, hz48, hzH, -, -⟩, -, -, -, -, -, -, -, -⟩ := hZ0
  have hrL0 := hrL
  obtain ⟨hr8, hrH, hracc, hr48⟩ := hrL0 (by omega)
  refine toSn2 impl ret hret _ sp st zzp (2 * n + 1) zzc (2 * n) M hal (by omega) hA
    (M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) r672 r128 (by omega) (by omega) (by omega)
    S hpc hsp h0 h1 h2 hmem (fun S1 M1 e1 e2 e3 e4 e5 e6 e7 e8 em hmf hrg q400 q168 q160 => ?_)
  -- the own spills
  have ws_in : ∀ r ∈ [(sp + 160, sp + 176), (sp + 400, sp + 408)], sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 752 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only; omega)
  have hk1 := keeps_own hC hmf hrg ws_in (fun j hj => by simp only [outside_cons, outside_nil, and_true]; omega)
  have hC1 := Ctx.keep hC hk1
  have hAn1 := Anc.keep hAn hk1 hl0A (Nat.le_trans hl0 hsok.2.2.2.2.2.1) (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexA) hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have ow : ∀ a k, Apart a k (sp - K) (K + 752) → M1.readLE a k = M.readLE a k := fun a k h =>
    hmf.readLE a k (outside_ws_of_win (lo := sp - K) (hi := sp + 752) (by unfold Apart at h; omega)
      (fun r hr => by have := ws_in r hr; omega))
  have rs1 : ∀ j, (j + 8 ≤ 160 ∨ 176 ≤ j ∧ j + 8 ≤ 400 ∨ 408 ≤ j) → M1.readLE (sp + j) 8 = M.readLE (sp + j) 8 :=
    fun j hj => hmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hst : Apart st 24 (sp - K) (K + 752) := hstw
  have h0' := ow st 8 (hst.mono (by omega) (Nat.le_refl _))
  have h1' := ow (st + 8) 8 (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _))
  have h2' := ow (st + 16) 8 (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _))
  have hl01 : l0 ≤ stCap M1 st := by
    have := hsok.2.2.2.2.2.1; simp only [stLen, stCap] at this hl0 ⊢; rw [h2']; omega
  have hZ1 := ZZ.keep hZ (LiveExt.refl R L) (fun a k w => hmf.accessible a k w) (Or.inl ⟨h0', h2'⟩) hl01
  have hzv1 : M1.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n) :=
    (ow zzp (8 * (2 * n + 1)) (Apart.mono hzzK (by omega) (Nat.le_refl _))).trans hzv
  have hrB1 : (stW M1 st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M1 st + 8 * stLen M1 st) ∨
      Apart rrp (8 * (2 * n)) (stW M1 st) (8 * stCap M1 st) := by
    simp only [stW, stLen, stCap] at hrB ⊢; rw [h0', h1', h2']; exact hrB
  have hinv1 : R.inv b L g (view R.rt L M1) := by
    refine FvModexp.Expmc.inv_frame hmf (fun r hr => Or.inr ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hrt.of_sub (by omega) (by omega)
  -- the call `stk.nat(2n)`
  have hC1' := hC1
  obtain ⟨-, hce1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw1, hsok1, -, hl01', hcap1, harr1, -, huw1, hsu1, hgl1, -, hstwb, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC1'
  have hlc1 := hsok1.2.2.2.2.2.1
  have hlen1 : stLen M1 st = stLen M st := h1'
  have hpre : SnPre R b L g sp st (2 * n) M1 := by
    refine ⟨CallW.CEnv.mono hce1 hK (Nat.le_refl _), hserv, hsok1,
      Apart.sub hstw1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega),
      fun hc => ⟨Apart.sub (harr1 hc).1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega), (harr1 hc).2⟩,
      by omega, by rw [hlen1]; omega, by rw [hlen1]; omega, hinv1, hgl1.2.2.2.2.2.2.2.2.2.2.1, hstwb,
      (in_stUp hsu1 (by simp only [stFree]; omega) (by simp only [stFree]; omega))⟩
  have hRA : RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) sn2Ret :=
    CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := StackNat.names)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 252
      (by decide) (by decide) (by decide)
  refine snCallK impl hap R hSN ret hret _ b L g sp (2 * n) st sn2Ret M1 r18 f29 hRA (by decide) hpre (by omega)
    (by omega) S1 e1 e2 e3 e4 e5 (e6.trans h18) (e7.trans h28) (e8.trans h29) em
    (fun S2 M2 L2 b2 f1 f2 f3 f4 f5 f6 f7 f8 f9 hS => ?_)
  have hk2 := keeps_sn hC1 (by omega) hS
  have hC2 := Ctx.keep hC1 hk2
  have hAn2 := Anc.keep hAn1 hk2 hl0A hl01 (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexA) hce1.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hS0 := hS
  obtain ⟨hx2, hb2, hinv2, hsok2, hlen2, -, -, hF2, -, -⟩ := hS0
  have hst2 := hk2.2.2.2.2.2.2.2.2.2.2.1
  have hlc2 := hsok2.2.2.2.2.2.1
  have hr2 : 2 * n ≤ StackNat.rnd (2 * n) := by simp only [StackNat.rnd]; omega
  have hl02 : l0 ≤ stCap M2 st := by simp only [stLen, stCap] at hlen2 hlc2 hl01' ⊢; omega
  have hZ2 := ZZ.keep hZ1 hx2 (fun a k w => hF2.accessible a k w) hst2 hl02
  have hZ1' := hZ1
  obtain ⟨⟨-, -, -, -, hzH1, -, -⟩, -, -, -, -, -, hzS1, hzU1, -⟩ := hZ1'
  have hzv2 : M2.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n) := by
    refine (held_sn hS (hzH1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (Apart.sub hzzK (Nat.le_refl _) (by omega) (by omega) (by omega)) (hzS1.mono (by omega) (Nat.le_refl _))
      ?_).trans hzv1
    exact (in_stUp hzU1 (by simp only [stFree]; omega) (by simp only [stFree]; omega)).mono (by omega) (Nat.le_refl _)
  obtain ⟨hrB2, hqr0⟩ := below_sn hS hrH hrB1
  have hrL2 : NatLive M2 R L2 rrp (2 * n) := fun _ =>
    ⟨hr8, hx2.held hrH, by rw [hF2.accessible, hmf.accessible]; exact hracc, hr48⟩
  have hcap2 : 0 < stCap M2 st := hk2.2.2.2.2.2.2.2.2.2.2.2 hcap1
  obtain ⟨a8, aH, aacc, a48⟩ := hsok2.2.2.2.2.1 hcap2
  have hqin : stW M2 st + 8 * l0 ≤ stW M2 st + 8 * stLen M1 st ∧
      stW M2 st + 8 * stLen M1 st + 8 * (2 * n) ≤ stW M2 st + 8 * stLen M2 st := by
    simp only [stLen] at hlen2 hl01' ⊢; omega
  have hqL : NatLive M2 R L2 (stW M2 st + 8 * stLen M1 st) (2 * n) := fun _ =>
    ⟨by omega, aH.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)),
      M2.accessible_sub aacc (Or.inr rfl) (by omega) (by omega), by omega⟩
  have hrt4 : Outside (sp - 4304) (4304 + 752) R.rt := hrt.of_sub (by omega) (by omega)
  have hfw : Apart (stFree M1 st).1 (stFree M1 st).2 (sp - 4304) (4304 + 752) :=
    Apart.sub (in_stUp huw1.symm (by simp only [stFree]; omega) (by simp only [stFree]; omega)).symm
      (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
  have sl : ∀ j, 24 ≤ j → j + 8 ≤ 752 → M2.readLE (sp + j) 8 = M1.readLE (sp + j) 8 := fun j a b =>
    slot_sn hS hrt4 (by omega) (Apart.sub hstw1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)) hfw j a b
  have hlenM2 : stLen M2 st = stLen M st + StackNat.rnd (2 * n) := by rw [hlen2, hlen1]
  refine reaches_mono (divStep impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW hserv ret hret b2 L2 g sp K n mp
    mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t (stW M2 st + 8 * stLen M1 st) rrp zzp zzc M2 r18 r29 f29 hKD hC2 hZ2 hzzK
    hzl hzv2 (norm_of_pow hzv2) hzzr hqin hqL hqr0.symm hrL2 hrW hrG hrS hrB2
    (by rw [sl 408 (by omega) (by omega), rs1 408 (by omega)]; exact r408)
    (by rw [sl 176 (by omega) (by omega), rs1 176 (by omega)]; exact r176)
    (by rw [sl 400 (by omega) (by omega)]; exact q400) (by rw [sl 160 (by omega) (by omega)]; exact q160)
    (by rw [sl 168 (by omega) (by omega)]; exact q168) ht
    (by rw [sl 224 (by omega) (by omega), rs1 224 (by omega)]; exact r224)
    (by rw [sl 128 (by omega) (by omega), rs1 128 (by omega)]; exact r128)
    hkk hmB hMo hM1 (by rw [hlenM2]; omega) (by rw [hlenM2]; exact hcF) (by rw [hlenM2]; rw [hlen1] at hb2; omega) hinv2
    L0 bA M0 hAn2 (by rw [hlen1] at hb2; exact ble2 hbA hb2) hl0A hexA
    S2 f1 f2 f3 f4 f5 f6 f7 f8 f9) (isReturn_mono fun s' h => ?_)
  rw [hlenM2] at h
  exact h

end FvModexp.Arm64.W2Pro
