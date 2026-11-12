import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2OneRet

/-!
# window-2 (arm64): from `oneJ` (fn+0x524) to the return — `oneSmall`/`oneLarge` + `afterOne`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem oneRet (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t rrp rrc xp xc yp ylen Y yi zp zc zzp zzc st n0 : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64)
    (he : Env R L g sp M) (hce : CallW.CEnv R L g sp 4304 752 M)
    (hn : 0 < n) (hn128 : n ≤ 128) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp) (hrr : Inp R L sp n M rrp) (hx : Inp R L sp n M xp)
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r544 : M.readLE (sp + 544) 8 = rrp) (r256 : M.readLE (sp + 256) 8 = n) (r264 : M.readLE (sp + 264) 8 = rrc)
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
    -- the stack
    (hsok : StkOK M R L st) (hn0 : n0 ≤ stLen M st) (hcap : 0 < stCap M st)
    (hfg : Apart (stFree M st).1 (stFree M st).2 (g + 16) 8)
    (harr : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4304) (4304 + 752) ∧
      Apart (stW M st) (8 * stCap M st) (g + 16) 8)
    (hfw : Apart (stFree M st).1 (stFree M st).2 (sp - 4304) (4304 + 752))
    (hslen : stLen M st + 5 * n + 3 ≤ 2 ^ 16) (hwba : M.accessible StackNat.wbA 4 false = true)
    (hstwb : Apart st 24 StackNat.wbA 4) (hstf : Apart st 24 (stFree M st).1 (stFree M st).2)
    (hmS : Apart mp (8 * n) st 24) (hmF : Apart mp (8 * n) (stFree M st).1 (stFree M st).2)
    (hrS : Apart rrp (8 * n) st 24) (hrF : Apart rrp (8 * n) (stFree M st).1 (stFree M st).2)
    (hxS : Apart xp (8 * n) st 24) (hxF : Apart xp (8 * n) (stFree M st).1 (stFree M st).2)
    (hyS : Apart yp (8 * ylen) st 24) (hyF : Apart yp (8 * ylen) (stFree M st).1 (stFree M st).2)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (5 * n) + blockSize (8 * (2 * n + 4)) true ≤ b)
    (r672 : M.readLE (sp + 672) 8 = st)
    (hokone : 4 < n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, n, n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneJ) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        OneChain R b L L2 b2 sp n st M M2 ∧
        RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29
          (M.readLE mp (8 * n)) (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) M2 s')) := by

  have hce0 := hce
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := hce0
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmkL := MakesliceLiveContract.of_codeIn hc hmk
  by_cases h4 : n ≤ 4
  · exact oneSmall impl ret hret _ R b L g sp n st M r18 f29 he hn h4 r736 r672 hinv S hpc hsp h0 h18 h28 h29 hmem
      (fun S' M' onep L' b' c1 c2 c3 c4 c5 c6 c7 c8 c9 hO =>
        reaches_mono (afterOne impl hap R hclr hmv hmk hSN hserv ret hret b L g sp n mp mc t rrp rrc xp xc yp ylen Y yi zp
        zc zzp zzc st n0 M r18 r29 f29 he hce hn hn128 hmc hmc' ht hm hrr hx r728 r736 r744 r224 r128 r544 r256 r264 r616
        r328 r320 hok hyl hyl' hy hY hyi hyi0 hzc hz hold hzz hzz8 hzzm hzzy hzz4 hzzs hzzF hro hty r664 r648 r168 r400
        r712 r704 hokz hokM hmw4 hnm hkk hmB hfe hsth hstw4 hsok hn0 hcap hfg harr hfw hslen hwba hstwb hstf hmS hmF hrS
        hrF hxS hxF hyS hyF hbud L' b' onep M' hO S' c1 c2 c3 c4 c5 c6 c7 c8 c9)
        (isReturn_mono fun s h => ⟨onep, h⟩))
  · exact oneLarge impl R hmkL ret hret _ b L g sp n st M r18 f29 he (by omega) (by omega) hd hro hty r736 r672
      ⟨hokone (by omega), by omega⟩ hinv S hpc hsp h0 h18 h28 h29 hmem
      (fun S' M' onep L' b' c1 c2 c3 c4 c5 c6 c7 c8 c9 hO =>
        reaches_mono (afterOne impl hap R hclr hmv hmk hSN hserv ret hret b L g sp n mp mc t rrp rrc xp xc yp ylen Y yi zp
        zc zzp zzc st n0 M r18 r29 f29 he hce hn hn128 hmc hmc' ht hm hrr hx r728 r736 r744 r224 r128 r544 r256 r264 r616
        r328 r320 hok hyl hyl' hy hY hyi hyi0 hzc hz hold hzz hzz8 hzzm hzzy hzz4 hzzs hzzF hro hty r664 r648 r168 r400
        r712 r704 hokz hokM hmw4 hnm hkk hmB hfe hsth hstw4 hsok hn0 hcap hfg harr hfw hslen hwba hstwb hstf hmS hmF hrS
        hrF hxS hxF hyS hyF hbud L' b' onep M' hO S' c1 c2 c3 c4 c5 c6 c7 c8 c9)
        (isReturn_mono fun s h => ⟨onep, h⟩))

end FvModexp.Arm64.W2Pro
