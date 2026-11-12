import FvModexp.Proofs.Arm64.Exp.W4DivM
import FvModexp.Proofs.Arm64.Exp.W4DivR
import FvModexp.Proofs.Arm64.Exp.W4Anc

/-!
# window-4 prologue (arm64): `divStep` — from the return of `stk.nat(2n)` #2 (`sn2Ret`, fn+0x3f0) to the function's `RET`

`toDiv` (argument loads) + `divCallK` (`RR = 2^(128n) mod m` by `nat.div`) + `rrRetC` (everything after `divRet`),
with the context moved through the division by `keeps_div`/`Ctx.keep`, `ZZ.keep`, `rem_div`, `slot_div`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

/-- the post of the window-4 function from `divRet` on, with the memory at `divRet` and the remainder abstracted -/
@[reducible] def DivRetPost (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g sp n mp mc Mv Xv t yp ylen Y yi zp zc st n0 zzp zzc lenM : Nat)
    (r18 r29 : BitVec 64) (s' : State) : Prop :=
  ∃ (M' : Memory) (L' : List (Nat × Nat)) (b' rp rl rc : Nat) (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory)
    (L2 : List (Nat × Nat)) (b2 : Nat),
    Anc R L0 sp K st M0 L' M' ∧ bA ≤ b' ∧ stLen M' st = lenM ∧
    M'.readLE rp (8 * rl) = 2 ^ (128 * n) % Mv ∧ RRPost R b' L' g sp n rp rl rc zzp zzc M' M1 rrp rrc ∧
    OneChain R b' L' L2 b2 sp n st M1 M2 ∧
    RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * lenM) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29 Mv Xv
      (2 ^ (128 * n) % Mv) M2 s'

/-- a range inside the stack above `l0` is apart from everything apart from that part -/
theorem free_of_up {a k st l0 : Nat} {M : Memory} (h : Apart a k (stUp M st l0).1 (stUp M st l0).2)
    (h1 : l0 ≤ stLen M st) (h2 : stLen M st ≤ stCap M st) :
    Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) := by
  simp only [stUp, Apart] at h ⊢; omega

theorem in_stUp {a k p q st l0 : Nat} {M : Memory} (h : Apart a k (stUp M st l0).1 (stUp M st l0).2)
    (h1 : stW M st + 8 * l0 ≤ p) (h2 : p + q ≤ stW M st + 8 * stCap M st) : Apart a k p q := by
  simp only [stUp, Apart] at h ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem divStep (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t qp rrp zzp zzc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K)
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [(rrp, 8 * (2 * n))] M)
    (hZ : ZZ R L g sp n mp xp yp ylen zp zc st l0 zzp zzc M) (hzzK : AW sp K zzp (8 * zzc)) (hzl : 2 * n + 1 ≤ zzc)
    (hzv : M.readLE zzp (8 * (2 * n + 1)) = 2 ^ (128 * n)) (hzN : NatNorm M zzp (2 * n + 1))
    (hzzr : Apart zzp (8 * zzc) rrp (8 * (2 * n)))
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (hqL : NatLive M R L qp (2 * n)) (hqr : Apart qp (8 * (2 * n)) rrp (8 * (2 * n)))
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (r408 : M.readLE (sp + 408) 8 = rrp) (r176 : M.readLE (sp + 176) 8 = 2 * n)
    (r400 : M.readLE (sp + 400) 8 = zzp) (r160 : M.readLE (sp + 160) 8 = 2 * n + 1)
    (r168 : M.readLE (sp + 168) 8 = zzc)
    (ht : t < 2 ^ 64) (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : stLen M st + 32 * n + 80 ≤ 2 ^ 16)
    (hcF : costF (stLen M st) (2 * n + 1) n ≤ costD)
    (hbud : costD + (blockSize (8 * n) true + stackNatCost (stLen M st) (17 * n) + blockSize (8 * (2 * n + 4)) true) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M) (hbA : bA + costD ≤ b)
    (hl0A : stLen M0 st ≤ l0) (hexA : ALoc R L0 st M0 (rrp, 8 * (2 * n)))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 sn2Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibExp.program.link impl).withExit ret) S
      (IsReturn (DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv t yp ylen Y yi zp zc st n0 zzp zzc (stLen M st) r18 r29)) := by
  have hC0 := hC
  obtain ⟨-, hce, hK, -, hn, hn128, -, hmc', hm, hmO, hmV, hnm, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, -, harr, hug, huw, hsu, hgl, -, -, -, -,
    r1016, r1024, r1032, -, -, -, -, r960, -, -, -⟩ := hC0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, -, -, -, -, -, -⟩ := hce0
  have hZ0 := hZ
  obtain ⟨⟨-, hzc40, hzacc, hz48, hzH, -, -⟩, -, -, -, -, -, hzS, hzU, -⟩ := hZ0
  have hlc := hsok.2.2.2.2.2.1
  have hst48 := hsok.2.2.2.1
  obtain ⟨hq8, -, -, hq48⟩ := hqL (by omega)
  obtain ⟨hr8, -, -, hr48⟩ := hrL (by omega)
  have hqa : stW M st + 8 * l0 ≤ qp := hqin.1
  have hqb : qp + 8 * (2 * n) ≤ stW M st + 8 * stCap M st := by have := hqin.2; omega
  refine toDiv impl ret hret _ sp st rrp zzp (2 * n + 1) zzc mp n mc M hal (by omega) hA
    (M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) r960 r408 r176 r400 r160 r168 r1016 r1024 r1032
    S hpc hsp hmem (fun S1 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 em => ?_)
  -- the division
  have hpre : DvPre R b costF costD L g sp K stkD st qp rrp n zzp (2 * n + 1) mp M := by
    refine ⟨hce, hKD, hserv, hgl, hn128, hn, hqL, (in_stUp huw.symm hqa hqb).symm,
      (in_stUp hug.symm hqa hqb).symm, hrL, hrW, hrG, by omega,
      M.accessible_sub hzacc (Or.inl rfl) (by omega) (by omega), by omega,
      hzH.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)),
      Apart.mono hzzK (by omega) (by omega), hm.1, hm.2.1, hm.2.2.1, hmO.2.1, hzN, hnm, hsok, hstw, harr,
      by omega, by omega, Apart.mono hzS (by omega) (Nat.le_refl _),
      free_of_up (Apart.mono hzU (by omega) (Nat.le_refl _)) hl0 hlc, hmO.2.2.1, free_of_up hmO.2.2.2.1 hl0 hlc,
      hqr, fun p hp => ?_, hcF, by omega, hinv⟩
    rcases hp with rfl | rfl
    · refine ⟨((in_stUp hzU hqa hqb).symm).mono (Nat.le_refl _) (by omega), (in_stUp hmO.2.2.2.1 hqa hqb).symm,
        (in_stUp hsu hqa hqb).symm, by unfold Apart; omega⟩
    · refine ⟨hzzr.symm.mono (Nat.le_refl _) (by omega), (hmO.2.2.2.2 _ (List.mem_singleton_self _)).symm, hrS, ?_⟩
      rcases hrB with h | h
      · unfold Apart; omega
      · exact h.sub (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
  refine divCallK impl hap R nsD stkD costD costF hDiv hnsD hnsW ret hret _ b L g sp K st qp rrp n zzp (2 * n + 1) zzc mp mc
    M r18 f29 hpre (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) S1 e1 e2
    (e3.trans h0) (e4.trans h1) (e5.trans h2) e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 (e17.trans h18) (e18.trans h28)
    (e19.trans h29) em (fun S2 M' L' b' r rl rc f1 f2 f3 f4 f5 f6 f7 f8 f9 hD => ?_)
  have hD0 := hD
  obtain ⟨-, hx, hb', hinv', ⟨hsok', hlen', hst'⟩, -, hF, -, -⟩ := hD0
  have hk := keeps_div hC hKD hqin hrL hrW hrG hD
  have hC' := Ctx.keep hC hk
  have hAn' := Anc.keep hAn hk hl0A (Nat.le_trans hl0 hlc) (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact hexA) hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  obtain ⟨hrl0, hrln, hrc, hrp, hra, hr48', hrh, hrw, hrS', hrF, hzr, hzz', hval⟩ :=
    rem_div hC hZ hzzK hKD hqin hrL hrW hrS hrB hzzr hzl hzv hMo hM1 hmB hD
  have hl0' : l0 ≤ stCap M' st := by
    have := hsok'.2.2.2.2.2.1; simp only [stLen, stCap] at hlen' this hl0 ⊢; omega
  have hZ' := ZZ.keep hZ hx (fun a k w => hF.accessible a k w) hst' hl0'
  have sl := fun j h1 h2 => slot_div (j := j) hC hqin hrW hD h1 h2
  refine reaches_mono (rrRetC impl hap R hclr hmv hmk hSN hserv ret hret b' L' g sp K n mp mc Mv xp xc Xv yp ylen Y yi
    zp zc st n0 l0 t r rl rc zzp zzc M' r18 r29 f29 _ hC' hZ' ht ((sl 224 (by omega) (by omega)).trans r224)
    ((sl 128 (by omega) (by omega)).trans r128) ((sl 168 (by omega) (by omega)).trans r168)
    ((sl 400 (by omega) (by omega)).trans r400) hkk hmB (by rw [hlen']; omega) (by rw [hlen']; omega) hinv' hrl0 hrln hrc hrp hra
    hr48' hrh hrw hrS' hrF hzr (zz_mid M' hzz' hrln) S2 f1 f2 f3 f4 f5 f6 f7 f8 f9) (isReturn_mono fun s' h => ?_)
  obtain ⟨M1, rrp', rrc, onep, M2, L2, b2, p1, p2, p3⟩ := h
  rw [hval, hlen'] at p3
  exact ⟨M', L', b', r, rl, rc, M1, rrp', rrc, onep, M2, L2, b2, hAn', ble1 hbA hb', hlen', hval, p1, p2, p3⟩

end FvModexp.Arm64.W4Pro
