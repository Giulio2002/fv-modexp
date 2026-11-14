import FvModexp.Proofs.Amd64.Exp.W4RR
import FvModexp.Proofs.Amd64.Exp.W4ORet2

set_option autoImplicit false

/-!
# window-4 prologue (amd64): from the return of the `RR` division (`divRet` = fn+0x5e5) to the return
(agent expmc s51; twin of `Arm64.W4RRRet`)

`rrFix` (RR gets exactly `n` words) → `oneRet`. Every fact `oneRet` needs at `rrJ` is moved from the memory at
`divRet` through `RRPost`'s frame (`R.rt ++ rw4 sp ++ [zz[0:n]]`, live set unchanged).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
/-- a range apart from the frame and from `zz` is outside `rw4 ++ [zz[0:n]]` -/
theorem out_rw4 {sp n zzp zzc a k : Nat} (hs : 4296 ≤ sp) (hn : n ≤ zzc)
    (hw : Apart a k (sp - 4296) (4296 + 0x3c0)) (hz : Apart zzp (8 * zzc) a k) :
    Outside a k (rw4 sp ++ [(zzp, zzp + 8 * n)]) := by
  unfold Apart at hw hz
  simp only [rw4, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- a held object apart from the window and from `zz` keeps its bytes `divRet → rrJ` -/
theorem rr_rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n rp rl rc zzp zzc rrp rrc a k : Nat}
    {M M1 : Memory} (hP : RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc) (hs : 4296 ≤ sp) (hn : n ≤ zzc)
    (hh : InRanges a k L ∨ Outside a k R.rt) (hw : Apart a k (sp - 4296) (4296 + 0x3c0))
    (hz : Apart zzp (8 * zzc) a k) : M1.readLE a k = M.readLE a k := by
  have ho := out_rw4 (n := n) hs hn hw hz
  rw [outside_append] at ho
  exact FvModexp.Expmc.held_readLE hh hP.1 hP.2.1 ho.1 ho.2

set_option maxRecDepth 20000 in
/-- a frame slot outside `rw4` (or a caller argument slot outside `R.rt`) keeps its word `divRet → rrJ` -/
theorem rr_slot {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n rp rl rc zzp zzc rrp rrc K : Nat}
    {M M1 : Memory} (hP : RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc) (hs : 4296 ≤ sp) (hn : n ≤ zzc)
    (hrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt) (hca : Outside (sp + 0x3c0) 0x20 R.rt)
    (hzw : Apart zzp (8 * zzc) (sp - 4296) (4296 + 0x3c0)) (hzc : Apart zzp (8 * zzc) (sp + 0x3c0) 0x20)
    (hK : (0x18 ≤ K ∧ K + 8 ≤ 0x100) ∨ (0x108 ≤ K ∧ K + 8 ≤ 0x128) ∨ (0x130 ≤ K ∧ K + 8 ≤ 0x360) ∨
      (0x368 ≤ K ∧ K + 8 ≤ 0x3c0) ∨ (0x3c0 ≤ K ∧ K + 8 ≤ 0x3e0)) :
    M1.readLE (sp + K) 8 = M.readLE (sp + K) 8 := by
  unfold Apart at hzw hzc
  refine hP.1.readLE _ _ ?_
  rw [outside_append, outside_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_cases h : K + 8 ≤ 0x3c0
    · exact hrt.of_sub (by omega) (by omega)
    · exact hca.of_sub (by omega) (by omega)
  · simp only [rw4, outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 from the return of the `RR` division to the return -/
theorem rrRet (hJ4 : FvModexp.Amd64.W4Pro.J4Spec) (hP01 : FvModexp.Amd64.W4Pro.P01Spec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc t rp rl rc xp yp ylen Y yi Mv zp zc zzp zzc st n0 fbp r : Nat}
    {M : Memory} {r5 : W64}
    (he : Env R L g fs sp M) (hd : Extracted.program.DataLoaded M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 12) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp) (hx : Inp R L sp n M xp)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])
    (hy : Inp R L sp ylen M yp) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi0 : 0 < yi)
    (s398 : M.readLE (sp + 0x398) 8 = ylen) (s390 : M.readLE (sp + 0x390) 8 = yp)
    (s3a8 : M.readLE (sp + 0x3a8) 8 = mp) (s3b0 : M.readLE (sp + 0x3b0) 8 = n) (s3b8 : M.readLE (sp + 0x3b8) 8 = mc)
    (hnm : NatNorm M mp n) (hMv : M.readLE mp (8 * n) = Mv)
    (s78 : M.readLE (sp + 0x78) 8 = 2 * n) (sd8 : M.readLE (sp + 0xd8) 8 = t)
    (s370 : M.readLE (sp + 0x370) 8 = xp) (s138 : M.readLE (sp + 0x138) 8 = n)
    (hfe : FinEnv sp st n0 fbp r M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g fs sp n M zp zc ∧ zp % 8 = 0)
    (hzz : Buf R L g fs sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hoz : 2 * n ≤ zc → Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) st 24 ∧
      Apart zp (8 * zc) (stFree M st).1 (stFree M st).2)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzzs : Apart zzp (8 * zzc) st 24) (hzzF : Apart zzp (8 * zzc) (stFree M st).1 (stFree M st).2)
    (hzx : Apart zzp (8 * zzc) xp (8 * n)) (hzca : Apart zzp (8 * zzc) (sp + 0x3c0) 0x20)
    (hzzz : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc))
    (r3d0 : M.readLE (sp + 0x3d0) 8 = zc) (r3c0 : M.readLE (sp + 0x3c0) 8 = zp)
    (hacc2 : M.accessible (sp + 0x3c0) 0x20 false = true) (hca : Outside (sp + 0x3c0) 0x20 R.rt)
    (hcF : Apart (sp + 0x3c0) 0x20 (stFree M st).1 (stFree M st).2) (hcS : Apart (sp + 0x3c0) 0x20 st 24)
    (hokm : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4])
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hfbp : fbp < 2 ^ 64)
    -- the stack
    (hsok : StkOK M R L st) (hn0 : n0 ≤ stLen M st) (hcap : 0 < stCap M st)
    (hstw : Apart st 24 (sp - 4296) (4296 + 0x3c0))
    (hstg : Apart st 24 (g + 16) 8) (hstf8 : Apart st 24 (fs - 8) 8)
    (hfg : Apart (stFree M st).1 (stFree M st).2 (g + 16) 8) (hff : Apart (stFree M st).1 (stFree M st).2 (fs - 8) 8)
    (harr : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4296) (4296 + 0x3c0) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8 ∧ Apart (stW M st) (8 * stCap M st) (fs - 8) 8)
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4296) (4296 + 0x3c0))
    (hslen : stLen M st + 17 * n + 3 ≤ 2 ^ 16) (hwba : M.accessible StackNat.wbA 4 false = true)
    (hstwb : Apart st 24 StackNat.wbA 4) (hstf : Apart st 24 (stFree M st).1 (stFree M st).2)
    (hmS : Apart mp (8 * n) st 24) (hmF : Apart mp (8 * n) (stFree M st).1 (stFree M st).2)
    (hxS : Apart xp (8 * n) st 24) (hxF : Apart xp (8 * n) (stFree M st).1 (stFree M st).2)
    (hyS : Apart yp (8 * ylen) st 24) (hyF : Apart yp (8 * ylen) (stFree M st).1 (stFree M st).2)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (17 * n) + 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (s3d8 : M.readLE (sp + 0x3d8) 8 = st) (hacc3 : M.accessible (sp + 0x3d8) 8 false = true)
    (hokone : 4 < n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, n, n])
    (s1a0 : M.readLE (sp + 0xa0) 8 = zzc) (s188 : M.readLE (sp + 0x188) 8 = zzp)
    -- the remainder `r` (= RR) of the division, in DI/SI/R8
    (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4296) (4296 + 0x3c0))
    (hrS : Apart rp (8 * rl) st 24) (hrF : Apart rp (8 * rl) (stFree M st).1 (stFree M st).2)
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 divRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h7 : S.regs 7 = BitVec.ofNat 64 rp) (h6 : S.regs 6 = BitVec.ofNat 64 rl) (h8 : S.regs 8 = BitVec.ofNat 64 rc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
        RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (17 * n) st n0 onep fbp
          Mv (M.readLE xp (8 * n)) (M.readLE rp (8 * rl)) M2 s') := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw', hfrt, hadx⟩ := he0
  have hzz0' := hzz
  obtain ⟨hzn2, hzzc, hzacc, hz48, hzh, hzw, hzg, hzf⟩ := hzz0'
  have hzn : n ≤ zzc := by omega
  have hc := codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive64.of_codeIn hc hmv
  have K : ∀ (S' : State) (rrp rrc : Nat), S'.rip = BitVec.ofNat 64 rrJ → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 n → S'.regs 3 = BitVec.ofNat 64 rrp → S'.regs 1 = BitVec.ofNat 64 n →
      S'.regs 2 = BitVec.ofNat 64 rrc → S'.regs 6 = BitVec.ofNat 64 zzc → S'.regs 7 = BitVec.ofNat 64 zzp →
      S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      RRPost R b L g sp n rp rl rc zzp zzc M S'.mem rrp rrc →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S'
        (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
          RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
          RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (17 * n) st n0 onep
            fbp Mv (M.readLE xp (8 * n)) (M.readLE rp (8 * rl)) M2 s') := by
    intro S' rrp rrc c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 hP
    generalize hM1 : S'.mem = M1 at hP
    have hP0 := hP
    obtain ⟨hF, hLF, hinv1, hrg1, hrv, hrr⟩ := hP0
    have acc1 : ∀ a k w, M1.accessible a k w = M.accessible a k w := fun a k w => hF.accessible a k w
    have rd : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x3c0) →
        Apart zzp (8 * zzc) a k → M1.readLE a k = M.readLE a k := fun a k hh hw hz => rr_rd hP hsp1 hzn hh hw hz
    have rs : ∀ K, ((0x18 ≤ K ∧ K + 8 ≤ 0x100) ∨ (0x108 ≤ K ∧ K + 8 ≤ 0x128) ∨ (0x130 ≤ K ∧ K + 8 ≤ 0x360) ∨
        (0x368 ≤ K ∧ K + 8 ≤ 0x3c0) ∨ (0x3c0 ≤ K ∧ K + 8 ≤ 0x3e0)) → M1.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K hK =>
      rr_slot hP hsp1 hzn hwrt hca hzw hzca hK
    have hstw' := hstw; have hzzs' := hzzs
    unfold Apart at hstw' hzzs'
    have hsth3 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
      rd _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
        (by unfold Apart; omega) (by unfold Apart; omega)
    have e1 : stW M1 st = stW M st := by simpa using hsth3 0 (by omega)
    have e2 : stLen M1 st = stLen M st := hsth3 8 (by omega)
    have e3 : stCap M1 st = stCap M st := hsth3 16 (by omega)
    have hFE : stFree M1 st = stFree M st := by simp only [stFree]; rw [e1, e2, e3]
    have hF' : MemFrame M M1 (R.rt ++ (rw4 sp ++ [(zzp, zzp + 8 * n)])) := by
      simpa only [List.append_assoc] using hF
    have he1 : Env R L g fs sp M1 :=
      Env.frame he hF' (out_rw4 hsp1 hzn (by unfold Apart at hgw ⊢; omega) (by unfold Apart at hzg ⊢; omega))
        (out_rw4 hsp1 hzn (by unfold Apart at hfw' ⊢; omega) (by unfold Apart at hzf ⊢; omega)) (LiveExt.refl R L)
    have hd1 : Extracted.program.DataLoaded M1 := by
      refine FvModexp.dataLoaded_frame64 hd hrg1 hro hF' ?_
      intro q hq hlt
      simp only [rw4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      have hw6 : ∀ a k, sp - 4296 ≤ a → a + k ≤ sp + 0x3c0 → M.accessible a k true = true := fun a k h1 h2 =>
        Arm64.Memory.accessible_sub (m := M) hwacc (Or.inr rfl) h1 (by omega)
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · exact hw6 _ _ (by simp only; omega) (by simp only; omega)
      · simp only at hlt ⊢; exact Arm64.Memory.accessible_sub (m := M) hzacc (Or.inr rfl) (by omega) (by omega)
    have inp1 : ∀ k p, Inp R L sp k M p → Inp R L sp k M1 p := fun k p h => inp_frame h hF
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
    have hfe1 : FinEnv sp st n0 fbp r M1 := by
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
      refine ⟨f1, f2, f3, by rw [acc1]; exact f4, by rw [rs 0x378 (by omega)]; exact f5,
        by rw [rs 0x340 (by omega)]; exact f6, by rw [rs 0x348 (by omega)]; exact f7,
        by rw [rs 0x350 (by omega)]; exact f8, f9, by rw [acc1]; exact f10, by rw [hsth3 16 (by omega)]; exact f11,
        f12, by rw [rs 0x380 (by omega)]; exact f13, by rw [rs 0x388 (by omega)]; exact f14, f15⟩
    have hsok1 : StkOK M1 R L st := by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsok
      refine ⟨s1, s2, by rw [acc1]; exact s3, s4, ?_, by rw [e2, e3]; exact s6, by rw [e3]; exact s7⟩
      intro hc'
      rw [e3] at hc'; rw [e1, e3]
      obtain ⟨q1, q2, q3, q4⟩ := s5 hc'
      exact ⟨q1, q2, by rw [acc1]; exact q3, q4⟩
    -- the `RR` input at `rrJ` (remainder or `zz`)
    have hrr1 : Inp R L sp n M1 rrp ∧ Apart rrp (8 * n) st 24 ∧ Apart rrp (8 * n) (stFree M st).1 (stFree M st).2 ∧
        rrc < 2 ^ 64 := by
      rcases hrr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, -⟩
      · exact ⟨⟨by rw [acc1]; exact hra, hr48, hrh, hrw⟩, hrS, hrF, by omega⟩
      · refine ⟨⟨by rw [acc1]; exact Arm64.Memory.accessible_sub (m := M) hzacc (Or.inl rfl) (Nat.le_refl _) (by omega),
          by omega, hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega)),
          by unfold Apart at hzw ⊢; omega⟩, by unfold Apart; omega, by unfold Apart at hzzF ⊢; omega, by omega⟩
    obtain ⟨hrr1, hrS1, hrF1, hrc1⟩ := hrr1
    have hbuf1 : ∀ p c, Buf R L g fs sp n M p c → Buf R L g fs sp n M1 p c := fun p c h => buf_frame h hF
    subst hM1
    refine ReachesRet.mono (oneRet hJ4 hP01 (Y := Y) (Mv := Mv) (yi := yi) hap hclr hmv hmk hmvok hwt hro hSN hserv he1 hd1 hn hn16 hmc hmc' ht (inp1 _ _ hm)
      hrr1 (inp1 _ _ hx) hok (inp1 _ _ hy) (by rw [hyr]; exact hY) hyi1 hyl hyl' hyi0
      (by rw [rs 0x398 (by omega)]; exact s398) (by rw [rs 0x390 (by omega)]; exact s390)
      (by rw [rs 0x3a8 (by omega)]; exact s3a8) (by rw [rs 0x3b0 (by omega)]; exact s3b0)
      (by rw [rs 0x3b8 (by omega)]; exact s3b8) hnm1 (by rw [hmr]; exact hMv)
      (by rw [rs 0x78 (by omega)]; exact s78) (by rw [rs 0xd8 (by omega)]; exact sd8)
      (by rw [rs 0x370 (by omega)]; exact s370) (by rw [rs 0x138 (by omega)]; exact s138)
      hfe1 hsth hzc (fun h => ⟨hbuf1 _ _ (hz h).1, (hz h).2⟩) hzzc (fun _ => ⟨hbuf1 _ _ hzz, hzz8⟩)
      (by rw [hFE]; exact hoz) (fun _ => by rw [hFE]; exact ⟨hzzm, hzzy, hzzs, hzzF⟩) (fun h _ => hzzz h)
      (by rw [rs 0x3d0 (by omega)]; exact r3d0) (by rw [rs 0x3c0 (by omega)]; exact r3c0)
      (by rw [acc1]; exact hacc2) hca (by rw [hFE]; exact hcF) hcS hokm hkk hmB hfbp hsok1 (by rw [e2]; exact hn0)
      (by rw [e3]; exact hcap) hstw hstg hstf8 (by rw [hFE]; exact hfg) (by rw [hFE]; exact hff)
      (by rw [e1, e3]; exact harr) (by rw [hFE]; exact hfw) (by rw [e2]; exact hslen) (by rw [acc1]; exact hwba)
      hstwb (by rw [hFE]; exact hstf) hmS (by rw [hFE]; exact hmF) hrS1 (by rw [hFE]; exact hrF1) hxS
      (by rw [hFE]; exact hxF) hyS (by rw [hFE]; exact hyF) (by rw [e2]; exact hbud) hinv1 hrc1 (by omega)
      (by omega) (by rw [rs 0x3d8 (by omega)]; exact s3d8) (by rw [acc1]; exact hacc3) hokone S' c1 c2 rfl c3 c4 c5 c6
      c7 c8 c9 c10 c11 c12 c13) ?_
    intro s' h
    obtain ⟨onep, M2, L2, b2, hC, hR⟩ := h
    rw [e2, hxr, hrv] at hR
    exact ⟨S'.mem, rrp, rrc, onep, M2, L2, b2, hP, hC, hR⟩
  exact rrFix impl hmvL b L g fs sp n rp rl rc zzp zzc M r5 he (by omega) hrl0 hrln hrc hra hr48 hrh hrw hzn hzzc
    hzacc hz48 hzh hzw hzr hzz0 (hmvok _ _ _ (by omega)) hinv s3b0 s1a0 s188 S hpc hsp hmem h7 h6 h8 h5 h14 hfs hx15
    hdf K

end FvModexp.Amd64.W4Pro
