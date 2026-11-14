import FvModexp.Proofs.Amd64.Exp.W4Snc
import FvModexp.Proofs.Amd64.Exp.W4P01Ret
import FvModexp.Proofs.Amd64.Exp.W4Posts2
import FvModexp.Proofs.Amd64.Exp.W4ORDefs

set_option autoImplicit false

/-!
# window-4 prologue (amd64): from the `stk.nat(17n)` call (after `one` / `powers`) to the return (agent expmc s50)

Twin of the arm64 `W4Pro.afterOne`: `snCall` → `p01Ret`. The facts `p01Ret` needs at `p01` are moved from the memory
`M` at `rrJ` through `OnePost` (`rrJ → snE`) and `SnPost` (the call); the table buffer `buf = stW' + 8·len` is in the
old free part of the stack (kept array) or in a fresh array.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf OneIn FinEnv)

theorem sub2 {b b1 b2 x y : Nat} (h1 : b - x ≤ b1) (h2 : b1 - y ≤ b2) : b - (x + y) ≤ b2 := by omega

set_option maxRecDepth 20000 in
/-- the composite frame `rrJ → p01` -/
theorem frames2 {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b2 g fs sp n onep st : Nat} {M M1 M2 : Memory}
    (hO : OnePost R L L1 b b1 g fs sp n M M1 onep) (hS : SnPost R b1 L1 L2 b2 g sp st (17 * n) M1 M2)
    (e1 : stW M1 st = stW M st) (e2 : stLen M1 st = stLen M st) (e3 : stCap M1 st = stCap M st) :
    MemFrame M M2 (R.rt ++ (ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st)) ∧
    LiveFrame M M2 L (stkWs M st) := by
  have hWE : stkWs M1 st = stkWs M st := by simp only [stkWs]; rw [e1, e2, e3]
  have hFO := hO.2.2.2.1; have hLO := hO.2.2.2.2.1; have hxO := hO.2.1
  have hFS := hS.2.2.2.2.2.2.2.1; have hLS := hS.2.2.2.2.2.2.2.2.1
  rw [hWE] at hFS hLS
  refine ⟨hFO.trans hFS (fun a k h => ⟨?_, ?_⟩), ⟨fun a k hin hout => by
    rw [hLS.readLE a k (hxO.inRanges_old hin) hout, hLO.readLE a k hin trivial]⟩⟩
  · simp only [outside_append] at h ⊢; exact ⟨h.1, h.2.1.1⟩
  · simp only [outside_append] at h ⊢; exact ⟨⟨h.1, h.2.1.2⟩, h.2.2⟩

set_option maxRecDepth 20000 in
theorem go2 {a sp st : Nat} {M : Memory} (hsp : 4296 ≤ sp) (hga : Apart a 8 (sp - 4296) (4296 + 0x3c0))
    (hstg : Apart st 24 a 8) (hfg : Apart (stFree M st).1 (stFree M st).2 a 8)
    (hlc : stLen M st ≤ stCap M st) :
    Outside a 8 (ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st) := by
  unfold Apart at hga hstg hfg; simp only at hfg
  simp only [ow, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega

theorem fe15 {n0 a b c d r : Nat} (hn0 : n0 ≤ a) (e2 : b = a) (hlen : c = b + r) (hc : c ≤ d) : n0 ≤ d := by omega

set_option maxRecDepth 20000 in
/-- `FinEnv` along the composite frame -/
theorem fin2 {R : RtInv} {sp st n0 fbp r : Nat} {M M2 : Memory}
    (hf : FinEnv sp st n0 fbp r M) (hrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt)
    (fr2 : MemFrame M M2 (R.rt ++ (ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st)))
    (hst : Apart st 24 (sp - 4296) (4296 + 0x3c0)) (hlc : stLen M st ≤ stCap M st)
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4296) (4296 + 0x3c0))
    (hcap : n0 ≤ M2.readLE (st + 16) 8) :
    FinEnv sp st n0 fbp r M2 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hf
  have rs : ∀ K, 0x340 ≤ K → K + 8 ≤ 0x390 → M2.readLE (sp + K) 8 = M.readLE (sp + K) 8 := by
    intro K h1 h2
    refine fr2.readLE _ _ ?_
    have hro : Outside (sp + K) 8 R.rt := hrt.of_sub (by omega) (by omega)
    unfold Apart at hst hfw; simp only at hfw
    simp only [ow, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hro, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨f1, f2, f3, by rw [fr2.accessible]; exact f4, by rw [rs 0x378 (by omega) (by omega)]; exact f5,
    by rw [rs 0x340 (by omega) (by omega)]; exact f6, by rw [rs 0x348 (by omega) (by omega)]; exact f7,
    by rw [rs 0x350 (by omega) (by omega)]; exact f8, f9, by rw [fr2.accessible]; exact f10, hcap, f12,
    by rw [rs 0x380 (by omega) (by omega)]; exact f13, by rw [rs 0x388 (by omega) (by omega)]; exact f14, f15⟩

set_option maxRecDepth 20000 in
/-- `one`'s facts at `p01` -/
theorem one_facts {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b1 b2 g sp n st onep : Nat} {M M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st (17 * n) M1 M2) (hxO : LiveExt R L L1)
    (e1 : stW M1 st = stW M st) (e2 : stLen M1 st = stLen M st) (e3 : stCap M1 st = stCap M st)
    (hlc : stLen M st ≤ stCap M st)
    (lah : InRanges (stW M st) (8 * stCap M st) L ∨ Outside (stW M st) (8 * stCap M st) R.rt)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt) (hstw : Apart st 24 (sp - 4296) (4296 + 0x3c0))
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4296) (4296 + 0x3c0)) (hsp : 4296 ≤ sp)
    (hbw : Apart (stW M2 st + 8 * stLen M st) (8 * (17 * n)) (sp - 4296) (4296 + 0x3c0))
    (honeC : (onep = sp + 0x148 ∧ n ≤ 4) ∨ (InRanges onep (8 * n) L1 ∧ InRanges onep (8 * n) R.rt ∧
      ApartAll onep (8 * n) L ∧ M1.accessible onep (8 * n) true = true ∧ onep + 8 * n ≤ 2 ^ 48 ∧ onep % 8 = 0))
    (hone1O : M1.readLE onep (8 * n) = 1) :
    OneIn R L2 sp n M2 onep ∧ M2.readLE onep (8 * n) = 1 ∧
    Apart (stW M2 st + 8 * stLen M st) (8 * (17 * n)) onep (8 * n) ∧
    (∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x3c0) → Apart a k onep (8 * n)) := by
  have hxS2 := hS.1
  have hFS := hS.2.2.2.2.2.2.2.1
  have hlc1 : stLen M1 st ≤ stCap M1 st := by rw [e2, e3]; exact hlc
  have hFE : stFree M1 st = stFree M st := by simp only [stFree]; rw [e1, e2, e3]
  have hWE : stkWs M1 st = stkWs M st := by simp only [stkWs]; rw [e1, e2, e3]
  have hfw' := hfw; have hstw' := hstw
  unfold Apart at hfw' hstw'; simp only at hfw'
  rcases honeC with ⟨rfl, h4⟩ | ⟨i1, i2, i3, i4, i5, i6⟩
  · refine ⟨Or.inr ⟨rfl, h4⟩, ?_, ?_, fun a k _ hw => ?_⟩
    · rw [hFS.readLE _ _ ?_]; exact hone1O
      have hro : Outside (sp + 0x148) (8 * n) R.rt := hrt.of_sub (by omega) (by omega)
      rw [hWE]
      simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hro, by omega⟩, by omega, by omega⟩
    · unfold Apart at hbw ⊢; omega
    · unfold Apart at hw ⊢; omega
  · have hpw := out_inR hrt i2
    have hsto : Apart st 24 onep (8 * n) := apart_held' i2 i3 hsth
    have hoF : Apart onep (8 * n) (stFree M st).1 (stFree M st).2 := by
      have := apart_held' i2 i3 lah; unfold Apart at this ⊢; simp only; omega
    refine ⟨Or.inl ⟨by rw [hFS.accessible]; exact Arm64.Memory.accessible_sub M1 i4 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _),
      i5, Or.inl (hxS2.inRanges_old i1), by unfold Apart; omega⟩, ?_, ?_, fun a k hh _ => apart_held' i2 i3 hh⟩
    · rw [sn_rd hS hlc1 (Or.inl i1) (by unfold Apart; omega) (by unfold Apart at hsto ⊢; omega)
        (by rw [hFE]; exact hoF) hsp]
      exact hone1O
    · have := buf_apart hS hlc1 (Or.inl i1) (fun _ => by rw [hFE]; exact hoF)
      rw [e2] at this; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ws_acc {R : RtInv} {L : List (Nat × Nat)} {g fs sp st : Nat} {M : Memory} (he : Env R L g fs sp M)
    (hstacc : M.accessible st 24 true = true) (hlc : stLen M st ≤ stCap M st)
    (laacc : 0 < stCap M st → M.accessible (stW M st) (8 * stCap M st) true = true) :
    ∀ r ∈ ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st, r.1 < r.2 →
      M.accessible r.1 (r.2 - r.1) true = true := by
  have hs1 : 4296 ≤ sp := he.2.1
  have hacc := he.2.2.2.1
  have hw6 : ∀ a k, sp - 4296 ≤ a → a + k ≤ sp + 0x3c0 → M.accessible a k true = true := fun a k h1 h2 =>
    Arm64.Memory.accessible_sub M hacc (Or.inr rfl) h1 (by omega)
  intro r hr hlt
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · have := ow_in sp r hr
      exact hw6 _ _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hw6 _ _ (by simp only; omega) (by simp only; omega)
  · simp only [stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hstacc
    · simp only at hlt ⊢
      exact Arm64.Memory.accessible_sub M (laacc (by omega)) (Or.inr rfl) (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 from the `stk.nat(17n)` call (after `one` / `powers`) to the return -/
theorem afterOne (hJ4 : FvModexp.Amd64.W4Pro.J4Spec) (hP01 : FvModexp.Amd64.W4Pro.P01Spec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc t rrp rrc xp yp ylen Y yi Mv zp zc zzp zzc st n0 fbp r : Nat}
    {M : Memory} {r5 : W64}
    (he : Env R L g fs sp M) (hd : Extracted.program.DataLoaded M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 12) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp) (hrr : Inp R L sp n M rrp) (hx : Inp R L sp n M xp)
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
    (hzzc : zzc < 2 ^ 40) (hzz : 2 * n ≤ zzc → Buf R L g fs sp n M zzp zzc ∧ zzp % 8 = 0)
    (hoz : 2 * n ≤ zc → Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) st 24 ∧
      Apart zp (8 * zc) (stFree M st).1 (stFree M st).2)
    (hozz : 2 * n ≤ zzc → Apart zzp (8 * zzc) mp (8 * n) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
      Apart zzp (8 * zzc) st 24 ∧ Apart zzp (8 * zzc) (stFree M st).1 (stFree M st).2)
    (hzzz : 2 * n ≤ zc → 2 * n ≤ zzc → Apart zp (8 * zc) zzp (8 * zzc))
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
    (hrS : Apart rrp (8 * n) st 24) (hrF : Apart rrp (8 * n) (stFree M st).1 (stFree M st).2)
    (hxS : Apart xp (8 * n) st 24) (hxF : Apart xp (8 * n) (stFree M st).1 (stFree M st).2)
    (hyS : Apart yp (8 * ylen) st 24) (hyF : Apart yp (8 * ylen) (stFree M st).1 (stFree M st).2)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (17 * n) + 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    -- after `one`
    {L1 : List (Nat × Nat)} {b1 onep : Nat} (S : State) (hO : OnePost R L L1 b b1 g fs sp n M S.mem onep)
    (hSl : OneSl sp rrp n rrc zzp zzc S.mem)
    (hpc : S.rip = BitVec.ofNat 64 snE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 (17 * n))
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        OneChain R b L L2 b2 sp n st M M2 ∧
        RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (17 * n) st n0 onep fbp
          Mv (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) M2 s') := by
  have hO0 := hO
  obtain ⟨heO, hxO, hbO, hFO, hLO, hinvO, hrgO, r328O, hone1O, honeC⟩ := hO0
  obtain ⟨e1, e2, e3⟩ := hdr_one hO hsth hstw
  have hFE : stFree S.mem st = stFree M st := by simp only [stFree]; rw [e1, e2, e3]
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw', hfrt, hadx⟩ := he0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  have hd1 : Extracted.program.DataLoaded S.mem := FvModexp.dataLoaded_frame64 hd hrgO hro hFO (fun r hr _ => by
    have := ow_in sp r hr; exact Arm64.Memory.accessible_sub M hwacc (Or.inr rfl) (by omega) (by omega))
  have hsok1 : StkOK S.mem R L1 st := by
    refine ⟨hst8, hxO.held hsth', by rw [hFO.accessible]; exact hstacc, hst48, ?_, by rw [e2, e3]; exact hlc,
      by rw [e3]; exact hcap40⟩
    intro hc
    rw [e3] at hc; rw [e1, e3]
    obtain ⟨q1, q2, q3, q4⟩ := hlive hc
    exact ⟨q1, hxO.held q2, by rw [hFO.accessible]; exact q3, q4⟩
  have hbud1 : stackNatCost (stLen M st) (17 * n) ≤ b1 := by
    by_cases h4 : 4 < n <;> simp only [h4, ite_true, ite_false] at hbO <;> omega
  have hpre1 : SnPre R b1 L1 g fs sp st (17 * n) S.mem := by
    refine ⟨Env.cenv heO hd1 hro, hserv, hsok1, hstw, by rw [e1, e3]; exact fun hc => ⟨(harr hc).1, (harr hc).2.1⟩,
      by omega, by rw [e2]; omega, by rw [e2]; exact hbud1, hinvO, by rw [hFO.accessible]; exact hwba, hstwb,
      by rw [hFE]; exact hstf⟩
  refine snCall hap hSN S hpre1 (by omega) hpc hsp hSl.2.2.2.2.2 h0 h3 h5 h14 hfs hx15 hdf ?_
  intro S2 L2 b2 c1 c2 c5 c14 cfs cx15 cdf c0 c1' hS
  have hc0 := c0 (by omega)
  rw [e2] at hc0
  have hS0 := hS
  obtain ⟨hxS2, hbS, hinvS, hsok2, hlen2, hkept, hfresh, hFS, hLS, hrgS, hmemS⟩ := hS0
  have hx2 : LiveExt R L L2 := hxO.trans hxS2
  have hlc1 : stLen S.mem st ≤ stCap S.mem st := by rw [e2, e3]; exact hlc
  have harr1 : 0 < stCap S.mem st → Apart (stW S.mem st) (8 * stCap S.mem st) (sp - 4296) (4296 + 0x3c0) ∧
      Apart (stW S.mem st) (8 * stCap S.mem st) (g + 16) 8 ∧ Apart (stW S.mem st) (8 * stCap S.mem st) (fs - 8) 8 := by
    rw [e1, e3]; exact harr
  obtain ⟨hba, hbb, hbh, hbw, hbg, hbf⟩ := buf_facts (fs := fs) hS hlc1 harr1 hwrt hgrt hfrt hn
  rw [e2] at hba hbb hbh hbw hbg hbf
  obtain ⟨fr2, lf2⟩ := frames2 hO hS e1 e2 e3
  have hrg2 : S2.mem.regions = M.regions := hrgS.trans hrgO
  have acc2 : ∀ a k w, S2.mem.accessible a k w = M.accessible a k w := fun a k w => by
    rw [hFS.accessible, hFO.accessible]
  have hgo2 := go2 hsp1 hgw hstg hfg hlc
  have hfo2 := go2 hsp1 hfw' hstf8 hff hlc
  have he2 : Env R L2 g fs sp S2.mem := Env.frame he fr2 hgo2 hfo2 hx2
  have hd2 : Extracted.program.DataLoaded S2.mem :=
    FvModexp.dataLoaded_frame64 hd hrg2 hro fr2 (ws_acc he hstacc hlc (fun _ => laacc))
  have rdo : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x3c0) → Apart a k st 24 →
      Apart a k (stFree M st).1 (stFree M st).2 → S2.mem.readLE a k = M.readLE a k :=
    fun a k hh hw hs hf => rd2 hO hS hsth hstw hlc hsp1 hh hw hs hf
  have rs : ∀ K, Outside (sp + K) 8 (ow sp) → 0x18 ≤ K → K + 8 ≤ 0x3c0 → S2.mem.readLE (sp + K) 8 = M.readLE (sp + K) 8 :=
    fun K hK h1 h2 => slot2 hO hS hsth hstw hfw hlc hwrt hsp1 hK h1 h2
  have hstw' := hstw; have hfw2 := hfw
  unfold Apart at hstw' hfw2; simp only at hfw2
  have rs1 : ∀ K, 0x10 ≤ K → K + 8 ≤ 0x3c0 → S2.mem.readLE (sp + K) 8 = S.mem.readLE (sp + K) 8 := by
    intro K h1 h2
    refine hFS.readLE _ _ ?_
    have hro' : Outside (sp + K) 8 R.rt := hwrt.of_sub (by omega) (by omega)
    simp only [stkWs, e1, e2, e3, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hro', by omega⟩, by omega, by omega⟩
  have hca0 : ∀ K, K + 8 ≤ 0x20 → S2.mem.readLE (sp + 0x3c0 + K) 8 = M.readLE (sp + 0x3c0 + K) 8 := by
    intro K hK
    have u1 := hcF; have u2 := hcS; unfold Apart at u1 u2; simp only at u1
    refine fr2.readLE _ _ ?_
    simp only [ow, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hca.of_sub (by omega) (by omega), by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  have bapL : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (stFree M st).1 (stFree M st).2 →
      Apart a k (stW S2.mem st + 8 * stLen M st) (8 * (17 * n)) := by
    intro a k hh hf
    have := buf_apart hS hlc1 (hh.imp hxO.inRanges_old id) (fun _ => by rw [hFE]; exact hf)
    rw [e2] at this; exact this
  have flip : ∀ a k c j, Apart a k c j → Apart c j a k := fun a k c j h => by unfold Apart at h ⊢; omega
  have inpT : ∀ k p, Inp R L sp k M p → Inp R L2 sp k S2.mem p := fun k p h =>
    ⟨by rw [acc2]; exact h.1, h.2.1, hx2.held h.2.2.1, h.2.2.2⟩
  have hxr : S2.mem.readLE xp (8 * n) = M.readLE xp (8 * n) := rdo _ _ hx.2.2.1 hx.2.2.2 hxS hxF
  have hrrr : S2.mem.readLE rrp (8 * n) = M.readLE rrp (8 * n) := rdo _ _ hrr.2.2.1 hrr.2.2.2 hrS hrF
  have hmr : S2.mem.readLE mp (8 * n) = M.readLE mp (8 * n) := rdo _ _ hm.2.2.1 hm.2.2.2 hmS hmF
  obtain ⟨hone2, hone12, hbo, hoA⟩ := one_facts hS hxO e1 e2 e3 hlc lah hsth hwrt hstw hfw hsp1 hbw honeC hone1O
  have hyi' : S2.mem.readLE (yp + 8 * (ylen - 1)) 8 = yi := by
    have hy4 := hy.2.2.2; have hyS' := hyS; have hyF' := hyF
    unfold Apart at hy4 hyS' hyF'
    rw [rdo _ _ ?_ (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega)]
    · exact hyi
    · rcases hy.2.2.1 with h1 | h1
      · exact Or.inl (h1.sub (by omega) (by omega))
      · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hnm2 : NatNorm S2.mem mp n := by
    rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2; have hmS' := hmS; have hmF' := hmF
      unfold Apart at hm4 hmS' hmF'
      rw [rdo _ _ ?_ (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega)]
      · exact h
      · rcases hm.2.2.1 with h1 | h1
        · exact Or.inl (h1.sub (by omega) (by omega))
        · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hbud2 : b - ((if 4 < n then blockSize (8 * n) true else 0) + stackNatCost (stLen M st) (17 * n)) ≤ b2 := by
    rw [e2] at hbS; exact sub2 hbO hbS
  have hbb2 : 2 * blockSize (8 * (2 * n + 4)) true ≤ b2 := by
    by_cases h4 : 4 < n <;> simp only [h4, ite_true, ite_false] at hbud2 <;> omega
  have hfe2 : FinEnv sp st n0 fbp r S2.mem :=
    fin2 hfe hwrt fr2 hstw hlc hfw (fe15 hn0 e2 hlen2 hsok2.2.2.2.2.2.1)
  have hP2 : PreT R L2 sp n mp mc yp ylen Y yi Mv onep st n0 fbp r S2.mem := by
    refine ⟨hd2, inpT _ _ hm, inpT _ _ hy, by rw [rdo _ _ hy.2.2.1 hy.2.2.2 hyS hyF]; exact hY, hyi',
      by rw [rs 0x398 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s398,
      by rw [rs 0x390 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s390,
      by rw [rs 0x3a8 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s3a8,
      by rw [rs 0x3b0 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s3b0,
      by rw [rs 0x3b8 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s3b8,
      hnm2, by rw [hmr]; exact hMv, hone2, hone12, by rw [rs1 0x328 (by omega) (by omega)]; exact r328O, hfe2,
      hx2.held hsth⟩
  have hs2 : PStatic R L2 g fs sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) (stW S2.mem st + 8 * stLen M st) (17 * n) S2.mem := by
    unfold PStatic
    exact ⟨he2, hn, by omega, hmc, hmc', by omega, inpT _ _ hm, Nat.le_refl _, by omega, hba, hbb, hbh, hbw, hbg, hbf,
      flip _ _ _ _ (bapL _ _ hm.2.2.1 hmF), hok⟩
  have oldO : ∀ p c, 2 * n ≤ c → Buf R L g fs sp n M p c → (Apart p (8 * c) mp (8 * n) ∧ Apart p (8 * c) yp (8 * ylen) ∧
      Apart p (8 * c) st 24 ∧ Apart p (8 * c) (stFree M st).1 (stFree M st).2) →
      OldB n mp yp ylen onep st (stW S2.mem st + 8 * stLen M st) (17 * n) p c := by
    intro p c _ hB ⟨a1, a2, a3, a4⟩
    exact ⟨a1, a2, bapL _ _ hB.2.2.2.2.1 a4, hoA _ _ hB.2.2.2.2.1 hB.2.2.2.2.2.1, a3⟩
  have hSl2 := hSl
  obtain ⟨q338, q100, qf8, qa0, q188, -⟩ := hSl2
  refine ReachesRet.mono (p01Ret hJ4 hP01 hap hclr hmv hmk hmvok hwt hro hs2 ht hP2 hbo (inpT _ _ hrr)
    (flip _ _ _ _ (bapL _ _ hrr.2.2.1 hrF)) (inpT _ _ hx) (flip _ _ _ _ (bapL _ _ hx.2.2.1 hxF))
    (bapL _ _ hy.2.2.1 hyF) (bapL _ _ hsth hstf)
    (by rw [rs 0x78 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s78)
    (by rw [rs 0xd8 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact sd8)
    (by rw [rs1 0x338 (by omega) (by omega)]; exact q338) (by rw [rs1 0xf8 (by omega) (by omega)]; exact qf8)
    ((rs1 0x100 (by omega) (by omega)).trans q100)
    (by rw [rs 0x370 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s370)
    (by rw [rs 0x138 (by simp only [ow, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega)]; exact s138)
    hinvS hyl hyl' hyi0 hzc (fun h => ⟨buf_ext hx2 (hz h).1 fr2, (hz h).2⟩) hzzc
    (fun h => ⟨buf_ext hx2 (hzz h).1 fr2, (hzz h).2⟩) (fun h => oldO _ _ h (hz h).1 (hoz h))
    (fun h => oldO _ _ h (hzz h).1 (hozz h)) hzzz
    (by rw [hca0 0x10 (by omega)]; exact r3d0) (by rw [show sp + 0x3c0 = sp + 0x3c0 + 0 by rfl, hca0 0 (by omega)]; exact r3c0)
    (by rw [rs1 0xa0 (by omega) (by omega)]; exact qa0) (by rw [rs1 0x188 (by omega) (by omega)]; exact q188)
    (by rw [acc2]; exact hacc2) hca (bapL _ _ (Or.inr hca) hcF) hokm (fun _ => by omega) (fun _ => hbb2)
    hkk hmB hfbp S2 c1 c2 rfl hc0 c1' c5 c14 cfs cx15 cdf) ?_
  intro s h
  rw [hxr, hrrr] at h
  refine ⟨S2.mem, L2, b2, ⟨fr2, lf2, hx2, hbud2, hsok2, by rw [hlen2, e2], ?_, ?_, hrg2, ?_⟩, h⟩
  · intro h; rw [← e1, ← e3]; exact hkept (by rw [e2, e3]; exact h)
  · intro h
    obtain ⟨q1, q2⟩ := hfresh (by rw [e2, e3]; exact h)
    exact ⟨q1, fun r hr => q2 r (hxO.mem_old hr)⟩
  · intro h; exact hmemS (by rw [e2, e3]; exact h)

end FvModexp.Amd64.W4Pro
