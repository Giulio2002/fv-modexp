import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2OneRet2
import FvModexp.Proofs.Arm64.Exp.W2RR

/-!
# window-2 (arm64): from the return of the `RR` division (`divRet` = fn+0x41c) to the return

`rrA`/`rrB` (RR gets exactly `n` words) → `oneRet`. Every fact `oneRet` needs at `oneJ` is moved from the memory at
`divRet` through `RRPost`'s frame (`R.rt ++ rw4 sp ++ [zz[0:n]]`, live set unchanged).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step)

set_option maxRecDepth 20000 in
/-- a held object apart from the window and from `zz` keeps its bytes `divRet → oneJ` -/
theorem rr_rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n rp rl rc zzp zzc rrp rrc a k : Nat} {M M1 : Memory}
    (hP : RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc) (hn : n ≤ zzc)
    (hh : InRanges a k L ∨ Outside a k R.rt) (hw : Apart a k (sp - 4288) (4288 + 752))
    (hz : Apart zzp (8 * zzc) a k) : M1.readLE a k = M.readLE a k := by
  unfold Apart at hw hz
  exact FvModexp.Expmc.held_readLE hh hP.1 hP.2.1
    (by simp only [rw4, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
/-- a window slot outside `rw4` keeps its word `divRet → oneJ` -/
theorem rr_slot {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n rp rl rc zzp zzc rrp rrc a : Nat} {M M1 : Memory}
    (hP : RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc) (hn : n ≤ zzc)
    (hrt : Outside (sp - 4288) (4288 + 752) R.rt) (hzw : Apart zzp (8 * zzc) (sp - 4288) (4288 + 752))
    (h1 : sp - 4288 ≤ a) (h2 : a + 8 ≤ sp + 752) (ho : Outside a 8 (rw4 sp)) : M1.readLE a 8 = M.readLE a 8 := by
  unfold Apart at hzw
  refine hP.1.readLE _ _ ?_
  rw [outside_append, outside_append]
  refine ⟨⟨hrt.of_sub h1 (by omega), ho⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem rrRet (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t rp rl rc xp xc yp ylen Y yi zp zc zzp zzc st n0 : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64)
    (he : Env R L g sp M) (hce : CallW.CEnv R L g sp 4304 752 M)
    (hn : 0 < n) (hn128 : n ≤ 128) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp) (hx : Inp R L sp n M xp)
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r616 : M.readLE (sp + 616) 8 = xp) (r328 : M.readLE (sp + 328) 8 = xc) (r320 : M.readLE (sp + 320) 8 = n)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hy : Inp R L sp ylen M yp) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0)
    (hold : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) st 24 ∧
      Apart zp (8 * zc) (stFree M st).1 (stFree M st).2)
    (hzz : Buf R L g sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzz4 : Apart zzp (8 * zzc) (sp - 4304) 16) (hzzs : Apart zzp (8 * zzc) st 24)
    (hzzF : Apart zzp (8 * zzc) (stFree M st).1 (stFree M st).2)
    (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r664 : M.readLE (sp + 664) 8 = zc) (r648 : M.readLE (sp + 648) 8 = zp)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r712 : M.readLE (sp + 712) 8 = ylen) (r704 : M.readLE (sp + 704) 8 = yp)
    (hokz : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4])
    (hokM : ∀ p d, R.ok (Extracted.program.contractAddr "runtime.memmove") [p, d, 8 * n])
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm : NatNorm M mp n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 752))
    (hsok : StkOK M R L st) (hn0 : n0 ≤ stLen M st) (hcap : 0 < stCap M st)
    (hfg : Apart (stFree M st).1 (stFree M st).2 (g + 16) 8)
    (harr : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4304) (4304 + 752) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8)
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4304) (4304 + 752))
    (hslen : stLen M st + 5 * n + 3 ≤ 2 ^ 16) (hwba : M.accessible StackNat.wbA 4 false = true)
    (hstwb : Apart st 24 StackNat.wbA 4) (hstf : Apart st 24 (stFree M st).1 (stFree M st).2)
    (hmS : Apart mp (8 * n) st 24) (hmF : Apart mp (8 * n) (stFree M st).1 (stFree M st).2)
    (hxS : Apart xp (8 * n) st 24) (hxF : Apart xp (8 * n) (stFree M st).1 (stFree M st).2)
    (hyS : Apart yp (8 * ylen) st 24) (hyF : Apart yp (8 * ylen) (stFree M st).1 (stFree M st).2)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (5 * n) + blockSize (8 * (2 * n + 4)) true ≤ b)
    (r672 : M.readLE (sp + 672) 8 = st)
    (hokone : 4 < n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, n, n])
    (hinv : R.inv b L g (view R.rt L M))
    -- the remainder `r` (= RR) of the division, in X3..X5
    (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40) (hrp : rp < 2 ^ 64)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4288) (4288 + 752))
    (hrS : Apart rp (8 * rl) st 24) (hrF : Apart rp (8 * rl) (stFree M st).1 (stFree M st).2)
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzx : Apart zzp (8 * zzc) xp (8 * n))
    (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 rp) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
        RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29
          (M.readLE mp (8 * n)) (M.readLE xp (8 * n)) (M.readLE rp (8 * rl)) M2 s')) := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hzz0' := hzz
  obtain ⟨hzn2, hzzc, hzacc, hz48, hzh, hzw, hzg⟩ := hzz0'
  have hzn : n ≤ zzc := by omega
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  -- the continuation at `oneJ`
  have K : ∀ (S' : State) (M1 : Memory) (rrp rrc : Nat), S'.pc = BitVec.ofNat 64 oneJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 n → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = f29 →
      S'.mem = M1 → RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc →
      Reaches ((LibW.program.link impl).withExit ret) S'
        (IsReturn (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
          RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
          RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29
            (M.readLE mp (8 * n)) (M.readLE xp (8 * n)) (M.readLE rp (8 * rl)) M2 s')) := by
    intro S' M1 rrp rrc c1 c2 c3 c4 c5 c6 c7 hP
    have hP0 := hP
    obtain ⟨hF, hLF, hinv1, hrg1, q544, q264, q256, q400, q168, hrv, hrr⟩ := hP0
    have flip : ∀ a k c j, Apart a k c j → Apart c j a k := fun a k c j h => by unfold Apart at h ⊢; omega
    have acc1 : ∀ a k w, M1.accessible a k w = M.accessible a k w := fun a k w => hF.accessible a k w
    have rd : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4288) (4288 + 752) →
        Apart zzp (8 * zzc) a k → M1.readLE a k = M.readLE a k := fun a k hh hw hz => rr_rd hP hzn hh hw hz
    have rs : ∀ K, (32 ≤ K ∧ K + 8 ≤ 168 ∨ 176 ≤ K ∧ K + 8 ≤ 256 ∨ 272 ≤ K ∧ K + 8 ≤ 304 ∨ 312 ≤ K ∧ K + 8 ≤ 400 ∨
        408 ≤ K ∧ K + 8 ≤ 544 ∨ 552 ≤ K ∧ K + 8 ≤ 600 ∨ 608 ≤ K ∧ K + 8 ≤ 752) →
        M1.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K hK =>
      rr_slot hP hzn hwrt hzw (by omega) (by omega) (by simp only [rw4, outside_cons, outside_nil, and_true]; omega)
    have hstw' := hstw4; unfold Apart at hstw'
    have hsth3 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
      rd _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
        (by unfold Apart; omega) (by unfold Apart at hzzs ⊢; omega)
    have e1 : stW M1 st = stW M st := by simpa using hsth3 0 (by omega)
    have e2 : stLen M1 st = stLen M st := hsth3 8 (by omega)
    have e3 : stCap M1 st = stCap M st := hsth3 16 (by omega)
    have hFE : stFree M1 st = stFree M st := by simp only [stFree]; rw [e1, e2, e3]
    have hgo : Outside (g + 16) 8 (rw4 sp ++ [(zzp, zzp + 8 * n)]) := by
      unfold Apart at hgw hzg
      simp only [rw4, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
    have hF' : MemFrame M M1 (R.rt ++ (rw4 sp ++ [(zzp, zzp + 8 * n)])) := by simpa only [List.append_assoc] using hF
    have he1 : Env R L g sp M1 := env_frame he hF' hgo
    have hce1 : CallW.CEnv R L g sp 4304 752 M1 := by
      refine CallW.CEnv.frame hce hF' hrg1 ?_ hgo
      intro r hr hlt
      simp only [rw4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hw6 : ∀ a k, sp - 4288 ≤ a → a + k ≤ sp + 752 → M.accessible a k true = true := fun a k h1 h2 =>
        M.accessible_sub hwacc (Or.inr rfl) h1 (by omega)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · simp only at hlt ⊢; exact M.accessible_sub hzacc (Or.inr rfl) (by omega) (by omega)
    have inp1 : ∀ k p, Inp R L sp k M p → Inp R L sp k M1 p := fun k p h =>
      ⟨by rw [acc1]; exact h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    have hmr : M1.readLE mp (8 * n) = M.readLE mp (8 * n) := rd _ _ hm.2.2.1 hm.2.2.2 hzzm
    have hxr : M1.readLE xp (8 * n) = M.readLE xp (8 * n) := rd _ _ hx.2.2.1 hx.2.2.2 hzx
    have hyw := hy.2.2.2; have hzy' := hzzy
    unfold Apart at hyw hzy'
    have hyr : M1.readLE yp (8 * ylen) = M.readLE yp (8 * ylen) := rd _ _ hy.2.2.1 hy.2.2.2 hzzy
    have hyi1 : M1.readLE (yp + 8 * (ylen - 1)) 8 = yi := by
      rw [rd _ _ ?_ (by unfold Apart; omega) (by unfold Apart; omega)]
      · exact hyi
      · rcases hy.2.2.1 with h1 | h1
        · exact Or.inl (h1.sub (by omega) (by omega))
        · exact Or.inr (h1.of_sub (by omega) (by omega))
    have hnm1 : NatNorm M1 mp n := by
      rcases hnm with h | h
      · exact Or.inl h
      · right
        have hm4 := hm.2.2.2; have hzm' := hzzm
        unfold Apart at hm4 hzm'
        rw [rd _ _ ?_ (by unfold Apart; omega) (by unfold Apart; omega)]
        · exact h
        · rcases hm.2.2.1 with h1 | h1
          · exact Or.inl (h1.sub (by omega) (by omega))
          · exact Or.inr (h1.of_sub (by omega) (by omega))
    have hfe1 : FinEnv sp g st n0 r29 ret M1 := by
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hfe
      have hrd : ∀ a, a = sp - 8 ∨ a = sp → M1.readLE a 8 = M.readLE a 8 := by
        intro a ha
        refine hF.readLE _ _ ?_
        have hro : Outside a 8 R.rt := hwrt.of_sub (by omega) (by omega)
        unfold Apart at hzw
        simp only [rw4, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hro, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega⟩
      have hgr : M1.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
        hF'.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hgo⟩)
      refine ⟨f1, f2, f3, by rw [acc1]; exact f4, f5, by rw [acc1]; exact f6, by rw [hgr]; exact f7, f8,
        by rw [rs 624 (by omega)]; exact f9, by rw [rs 552 (by omega)]; exact f10, by rw [rs 560 (by omega)]; exact f11,
        by rw [rs 568 (by omega)]; exact f12, f13, by rw [acc1]; exact f14, by rw [hsth3 16 (by omega)]; exact f15,
        f16, f17, by rw [hrd _ (Or.inl rfl)]; exact f18, by rw [hrd _ (Or.inr rfl)]; exact f19⟩
    have hsok1 : StkOK M1 R L st := by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsok
      refine ⟨s1, s2, by rw [acc1]; exact s3, s4, ?_, by rw [e2, e3]; exact s6, by rw [e3]; exact s7⟩
      intro hc'
      rw [e3] at hc'; rw [e1, e3]
      obtain ⟨q1, q2, q3, q4⟩ := s5 hc'
      exact ⟨q1, q2, by rw [acc1]; exact q3, q4⟩
    -- the `RR` input at `oneJ` (remainder or `zz`)
    have hrr1 : Inp R L sp n M1 rrp ∧ Apart rrp (8 * n) st 24 ∧ Apart rrp (8 * n) (stFree M st).1 (stFree M st).2 := by
      rcases hrr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, -⟩
      · exact ⟨⟨by rw [acc1]; exact hra, hr48, hrh, hrw⟩, hrS, hrF⟩
      · refine ⟨⟨by rw [acc1]; exact M.accessible_sub hzacc (Or.inl rfl) (Nat.le_refl _) (by omega), by omega,
          hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega)),
          by unfold Apart at hzw ⊢; omega⟩, by unfold Apart at hzzs ⊢; omega, by unfold Apart at hzzF ⊢; omega⟩
    obtain ⟨hrr1, hrS1, hrF1⟩ := hrr1
    have hrrv : M1.readLE rrp (8 * n) = M.readLE rp (8 * rl) := hrv
    refine reaches_mono (oneRet impl hap R hclr hmv hmk hSN hserv ret hret b L g sp n mp mc t rrp rrc xp xc yp ylen Y yi
      zp zc zzp zzc st n0 M1 r18 r29 f29 he1 hce1 hn hn128 hmc hmc' ht (inp1 _ _ hm) hrr1 (inp1 _ _ hx)
      (by rw [rs 728 (by omega)]; exact r728) (by rw [rs 736 (by omega)]; exact r736)
      (by rw [rs 744 (by omega)]; exact r744) (by rw [rs 224 (by omega)]; exact r224)
      (by rw [rs 128 (by omega)]; exact r128) q544 q256 q264
      (by rw [rs 616 (by omega)]; exact r616) (by rw [rs 328 (by omega)]; exact r328)
      (by rw [rs 320 (by omega)]; exact r320) hok hyl hyl' (inp1 _ _ hy) (by rw [hyr]; exact hY) hyi1 hyi0 hzc
      (fun h => ⟨buf_frame (hz h).1 hF, (hz h).2⟩) (by rw [hFE]; exact hold) (buf_frame hzz hF) hzz8 hzzm hzzy hzz4 hzzs
      (by rw [hFE]; exact hzzF) hro hty
      (by rw [rs 664 (by omega)]; exact r664) (by rw [rs 648 (by omega)]; exact r648) q168 q400
      (by rw [rs 712 (by omega)]; exact r712) (by rw [rs 704 (by omega)]; exact r704)
      hokz hokM hmw4 hnm1 (by rw [hmr]; exact hkk) (by rw [hmr]; exact hmB) hfe1 hsth hstw4 hsok1 (by rw [e2]; exact hn0)
      (by rw [e3]; exact hcap) (by rw [hFE]; exact hfg) (by rw [e1, e3]; exact harr) (by rw [hFE]; exact hfw)
      (by rw [e2]; exact hslen) (by rw [acc1]; exact hwba) hstwb (by rw [hFE]; exact hstf) hmS (by rw [hFE]; exact hmF)
      hrS1 (by rw [hFE]; exact hrF1) hxS (by rw [hFE]; exact hxF) hyS (by rw [hFE]; exact hyF) (by rw [e2]; exact hbud)
      (by rw [rs 672 (by omega)]; exact r672) hokone hinv1 S' c1 c2 c3 c4 c5 c6 c7) ?_
    refine isReturn_mono fun s' h => ?_
    obtain ⟨onep, M2, L2, b2, hC, hR⟩ := h
    rw [e2, hmr, hxr, hrrv] at hR
    exact ⟨M1, rrp, rrc, onep, M2, L2, b2, hP, hC, hR⟩
  by_cases hrn : rl = n
  · subst hrn
    exact rrA impl ret hret _ R L g sp rl rp rl rc zzp zzc M r18 f29 he (by omega) (Nat.le_refl _) (by omega) hrc hrp
      (Nat.le_refl _) (by unfold Apart at hrw ⊢; omega) b hinv (by omega) hzzc r736 r168 r400 S hpc hsp h3 h4 h5 h18
      h28 h29 hmem K
  · exact rrB impl R hmvL ret hret _ L g sp n rp rl rc zzp zzc M r18 f29 he (by omega) hrl0 (by omega) hrc hra hr48 hrh
      (by unfold Apart at hrw ⊢; omega) hzn hzzc hzacc hz48 hzh hzw hzr hzz0
      (hserv.2.1 _ _ _ (by omega)) b hinv r736 r168 r400 S hpc hsp h3 h4 h5 h18 h28 h29 hmem K

end FvModexp.Arm64.W2Pro
