import FvModexp.Proofs.Arm64.Exp.W4LshS

/-!
# window-4 prologue (arm64): `sn1Step` — from the entry of `RR := stk.nat(2n)` (#1, return `sn1Ret`) to the function's
`RET` (nat.go:1397). The context `Ctx` (with no extra range, `l0` = the stack length here) is established at this call;
after it, `RR` (the new stack nat, above `l0`) becomes the context's extra range (`Ctx.addEx`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

theorem obj_addEx {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 a k : Nat} {ex : List (Nat × Nat)} {e : Nat × Nat}
    {M : Memory} (h : Obj R L sp K st l0 ex M a k)
    (he : (stW M st + 8 * l0 ≤ e.1 ∧ e.1 + e.2 ≤ stW M st + 8 * stCap M st)) :
    Obj R L sp K st l0 (e :: ex) M a k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun e' he' => ?_⟩
  rcases List.mem_cons.1 he' with rfl | he'
  · exact in_stUp h4 he.1 he.2
  · exact h5 e' he'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a range inside the stack above `l0` becomes an extra range of the context -/
theorem Ctx.addEx {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {e : Nat × Nat} {M : Memory} (h : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    (he : (stW M st + 8 * l0 ≤ e.1 ∧ e.1 + e.2 ≤ stW M st + 8 * stCap M st)) :
    Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 (e :: ex) M := by
  obtain ⟨he', hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960, r904, r328, r320⟩ := h
  exact ⟨he', hce, hK, hK20, hn, hn128, hmc, hmc', hm, obj_addEx hmO he, hmV, hnm, hx, obj_addEx hxO he, hxv, hy,
    obj_addEx hyO he, hY, hyi, hyi0, hyl, hyl', hzc,
    fun h2 => ⟨(hz h2).1, (hz h2).2.1, obj_addEx (hz h2).2.2.1 he, (hz h2).2.2.2.1, (hz h2).2.2.2.2⟩,
    hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, obj_addEx hgO he, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960, r904, r328, r320⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sn1Step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibExp.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg34.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [] M) (hl0e : stLen M st = l0)
    (ht : t < 2 ^ 64) (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcF : costF (l0 + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD)
    (hbud : stackNatCost l0 (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l0 + StackNat.rnd (2 * n)) (2 * n) +
      (costD + (blockSize (8 * n) true + stackNatCost (l0 + 2 * StackNat.rnd (2 * n)) (17 * n) +
        blockSize (8 * (2 * n + 4)) true)))) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbA : bA + (stackNatCost l0 (2 * n) + (makeCost (1 + 128 * n / 64 + 1) +
      (stackNatCost (l0 + StackNat.rnd (2 * n)) (2 * n) + costD))) ≤ b) (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 snE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h30 : S.regs 30 = BitVec.ofNat 64 sn1Ret)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibExp.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ zzp zzc : Nat, (2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L0) ∧
        DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv t yp ylen Y yi zp zc st n0 zzp zzc
        (l0 + 2 * StackNat.rnd (2 * n)) r18 r29 s')) := by
  have hC0 := hC
  obtain ⟨-, hce, hK, -, hn, hn128, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, hcap, harr, -, huw, hsu, hgl, -, hstwb, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC0
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, -, -, -, -, -⟩ := hce0
  have hlc := hsok.2.2.2.2.2.1
  have hst48 := hsok.2.2.2.1
  have hr2 : 2 * n ≤ StackNat.rnd (2 * n) := by simp only [StackNat.rnd]; omega
  have hpre : SnPre R b L g sp st (2 * n) M := by
    refine ⟨CallW.CEnv.mono hce hK (Nat.le_refl _), hserv, hsok,
      Apart.sub hstw (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega),
      fun hc => ⟨Apart.sub (harr hc).1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega), (harr hc).2⟩,
      by omega, by rw [hl0e]; omega, by rw [hl0e]; omega, hinv, hgl.2.2.2.2.2.2.2.2.2.2.1, hstwb,
      (in_stUp hsu (by simp only [stFree]; omega) (by simp only [stFree]; omega))⟩
  have hRA : RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) sn1Ret :=
    CallW.retAddr_restrict hap (cs := Extracted.seg34) (ns := StackNat.names)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 229
      (by decide) (by decide) (by decide)
  refine snCallK impl hap R hSN ret hret _ b L g sp (2 * n) st sn1Ret M r18 f29 hRA (by decide) hpre (by omega)
    (by omega) S hpc hsp h0 h1 h30 h18 h28 h29 hmem (fun S2 M2 L2 b2 f1 f2 f3 f4 f5 f6 f7 f8 f9 hS => ?_)
  have hk := keeps_sn hC (by omega) hS
  have hC2 := Ctx.keep hC hk
  have hAn2 := Anc.keep hAn hk hl0A (by rw [← hl0e]; exact hlc) (fun e he => by simp at he) hce.2.2.2.2.2.2.2.2.2.2.1 hK0
  have hS0 := hS
  obtain ⟨hx2, hb2, hinv2, hsok2, hlen2, -, -, -, -, -⟩ := hS0
  have hlc2 := hsok2.2.2.2.2.2.1
  rw [hl0e] at f3 hlen2
  have hin : stW M2 st + 8 * l0 ≤ (stW M2 st + 8 * l0, 8 * (2 * n)).1 ∧
      (stW M2 st + 8 * l0, 8 * (2 * n)).1 + (stW M2 st + 8 * l0, 8 * (2 * n)).2 ≤ stW M2 st + 8 * stCap M2 st := by
    simp only [stLen, stCap] at hlen2 hlc2 ⊢; omega
  have hC3 := Ctx.addEx hC2 hin
  have hC3' := hC2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hcap2, -, hug2, huw2, hsu2, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC3'
  obtain ⟨a8, aH, aacc, a48⟩ := hsok2.2.2.2.2.1 hcap2
  have hrL : NatLive M2 R L2 (stW M2 st + 8 * l0) (2 * n) := fun _ =>
    ⟨by omega, aH.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)),
      M2.accessible_sub aacc (Or.inr rfl) (by omega) (by omega), by omega⟩
  have hrt4 : Outside (sp - 4304) (4304 + 1040) R.rt := hrt.of_sub (by omega) (by omega)
  have hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4304) (4304 + 1040) :=
    Apart.sub (in_stUp huw.symm (by simp only [stFree]; omega) (by simp only [stFree]; omega)).symm
      (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
  have sl : ∀ j, 24 ≤ j → j + 8 ≤ 1040 → M2.readLE (sp + j) 8 = M.readLE (sp + j) 8 := fun j a b =>
    slot_sn hS hrt4 (by omega) (Apart.sub hstw (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)) hfw j a b
  have hlenE : stLen M2 st = l0 + StackNat.rnd (2 * n) := hlen2
  have h2r : l0 + StackNat.rnd (2 * n) + StackNat.rnd (2 * n) = l0 + 2 * StackNat.rnd (2 * n) := by omega
  refine reaches_mono (lshStep impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL hserv
    ret hret b2 L2 g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t (stW M2 st + 8 * l0) M2 r18 r29 f29 hKD hKL hC3
    hrL (in_stUp huw2.symm hin.1 hin.2).symm (in_stUp hug2.symm hin.1 hin.2).symm (in_stUp hsu2 hin.1 hin.2).symm
    (Or.inl ⟨Nat.le_refl _, by rw [hlenE]; omega⟩) ht
    (by rw [sl 224 (by omega) (by omega)]; exact r224) (by rw [sl 128 (by omega) (by omega)]; exact r128)
    hkk hmB hMo hM1 (by rw [hlenE]; omega) (cf_eq hcF (by rw [hlenE]; omega)) (by rw [hlenE, h2r]; rw [hl0e] at hb2; omega) hinv2
    L0 bA M0 hAn2 (by rw [hlenE]; rw [hl0e] at hb2; exact ble2 hbA hb2) hl0A
    (aloc_of_anc hAn2 hl0A (cap8 hlenE hr2 hlc2))
    S2 f1 f2 f3 f5 f6 f7 f8 f9) (isReturn_mono fun s' h => ?_)
  obtain ⟨zzp, zzc, hfr, h⟩ := h
  refine ⟨zzp, zzc, hfr, ?_⟩
  rw [hlenE, Nat.add_assoc, ← Nat.two_mul] at h
  exact h

end FvModexp.Arm64.W4Pro
