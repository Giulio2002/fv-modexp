import FvModexp.Proofs.Amd64.Exp.W4ORet
import FvModexp.Proofs.Amd64.Exp.W4OneL

set_option autoImplicit false

/-!
# window-4 prologue (amd64): from the RR join `rrJ` to the return — `oneSmall` / `oneLarge` + `afterOne`
(agent expmc s50; twin of the arm64 `W4Pro.oneRet`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf OneIn FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 from the RR join (`one`, `powers`, `stk.nat(17n)`, table, …) to the return -/
theorem oneRet {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    {rrc : Nat} (hrc : rrc < 2 ^ 64) (hzp : zzp < 2 ^ 64) (hzc' : zzc < 2 ^ 64)
    (s3d8 : M.readLE (sp + 0x3d8) 8 = st) (hacc3 : M.accessible (sp + 0x3d8) 8 false = true)
    (hokone : 4 < n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, n, n])
    (S : State) (hpc : S.rip = BitVec.ofNat 64 rrJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 rrp) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (h2 : S.regs 2 = BitVec.ofNat 64 rrc) (h6 : S.regs 6 = BitVec.ofNat 64 zzc) (h7 : S.regs 7 = BitVec.ofNat 64 zzp)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        OneChain R b L L2 b2 sp n st M M2 ∧
        RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (17 * n) st n0 onep fbp
          Mv (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) M2 s') := by
  have hc := codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmkL := MakesliceLiveContract64.of_codeIn hc hmk
  have hrp : rrp < 2 ^ 64 := by have := hrr.2.1; omega
  have K : ∀ (S' : State) (onep : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) → S'.regs 0 = BitVec.ofNat 64 st →
      S'.regs 3 = BitVec.ofNat 64 (17 * n) → S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      OnePost R L L' b b' g fs sp n M S'.mem onep → OneSl sp rrp n rrc zzp zzc S'.mem →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S'
        (fun s' => ∃ (onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
          OneChain R b L L2 b2 sp n st M M2 ∧
          RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (17 * n) st n0 onep fbp
            Mv (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) M2 s') :=
    fun S' onep L' b' c1 c2 c3 c4 c5 c6 c7 c8 c9 hO hSl =>
      ReachesRet.mono (afterOne hap hclr hmv hmk hmvok hwt hro hSN hserv he hd hn hn16 hmc hmc' ht hm hrr hx hok hy hY hyi
        hyl hyl' hyi0 s398 s390 s3a8 s3b0 s3b8 hnm hMv s78 sd8 s370 s138 hfe hsth hzc hz hzzc hzz hoz hozz hzzz r3d0
        r3c0 hacc2 hca hcF hcS hokm hkk hmB hfbp hsok hn0 hcap hstw hstg hstf8 hfg hff harr hfw hslen hwba hstwb hstf
        hmS hmF hrS hrF hxS hxF hyS hyF hbud hinv S' hO hSl c1 c2 c3 c4 c5 c6 c7 c8 c9) (fun s h => ⟨onep, h⟩)
  by_cases h4 : n ≤ 4
  · exact oneSmall impl he hn h4 hrp (by omega) hrc hzp hzc' s3b0 s78 s3d8 hacc3 hinv S hpc hsp hmem h0 h3 h1 h2 h6 h7
      h5 h14 hfs hx15 hdf K
  · exact oneLarge impl hmkL he (by omega) (by omega) hd hrp (by omega) hrc hzp hzc' s3b0 s78 s3d8 hacc3 hca
      ⟨hokone (by omega), by omega⟩ hinv S hpc hsp hmem h0 h3 h1 h2 h6 h7 h5 h14 hfs hx15 hdf K

end FvModexp.Amd64.W4Pro
