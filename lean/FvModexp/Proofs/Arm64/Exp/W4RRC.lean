import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4Ctx
import FvModexp.Proofs.Arm64.Exp.W4RRRet

/-!
# window-4 (arm64): `rrRet` stated over the context `Ctx` (divRet → RET)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

/-- the facts about `zz` (the `lsh` result) at `divRet` -/
@[reducible] def ZZ (R : RtInv) (L : List (Nat × Nat)) (g sp n mp xp yp ylen zp zc st l0 zzp zzc : Nat) (M : Memory) :
    Prop :=
  Buf R L g sp n M zzp zzc ∧ zzp % 8 = 0 ∧ Apart zzp (8 * zzc) mp (8 * n) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
  Apart zzp (8 * zzc) xp (8 * n) ∧ Apart zzp (8 * zzc) (sp - 4304) 16 ∧ Apart zzp (8 * zzc) st 24 ∧
  Apart zzp (8 * zzc) (stUp M st l0).1 (stUp M st l0).2 ∧ (2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem rrRetC (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t rp rl rc zzp zzc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (ex : List (Nat × Nat))
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    (hZ : ZZ R L g sp n mp xp yp ylen zp zc st l0 zzp zzc M)
    (ht : t < 2 ^ 64) (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n)
    (hslen : stLen M st + 17 * n + 3 ≤ 2 ^ 16)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (17 * n) + blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40) (hrp : rp < 2 ^ 64)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4288) (4288 + 1040))
    (hrS : Apart rp (8 * rl) st 24) (hrF : Apart rp (8 * rl) (stFree M st).1 (stFree M st).2)
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 rp) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
        RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29
          Mv Xv (M.readLE rp (8 * rl)) M2 s')) := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960, r904, r328, r320⟩ := hC
  obtain ⟨hzz, hzz8, hzzm, hzzy, hzzx, hzz4, hzzs, hzzU, hzzz⟩ := hZ
  have hlc := hsok.2.2.2.2.2.1
  -- the free part lies in the stack above `l0`
  have fr : ∀ a k, Apart a k (stUp M st l0).1 (stUp M st l0).2 → Apart a k (stFree M st).1 (stFree M st).2 := by
    intro a k h; simp only [stUp, stFree] at h ⊢; unfold Apart at h ⊢; omega
  have frl : ∀ a k, Apart (stUp M st l0).1 (stUp M st l0).2 a k → Apart (stFree M st).1 (stFree M st).2 a k := by
    intro a k h; simp only [stUp, stFree] at h ⊢; unfold Apart at h ⊢; omega
  have w4 : ∀ a k, AW sp K a k → Apart a k (sp - 4304) (4304 + 1040) := by
    intro a k h; simp only [AW, Apart] at h ⊢; omega
  have w16 : ∀ a k, AW sp K a k → Apart a k (sp - 4304) 16 := by
    intro a k h; simp only [AW, Apart] at h ⊢; omega
  have hsv : (2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) st 24 ∧
      Apart zp (8 * zc) (stFree M st).1 (stFree M st).2) := by
    intro h
    obtain ⟨-, -, o, a1, a2⟩ := hz h
    exact ⟨hzzz h, a1, a2, w16 _ _ o.2.1, o.2.2.1, fr _ _ o.2.2.2.1⟩
  have hwba := hgl.2.2.2.2.2.2.2.2.2.2.1
  refine reaches_mono (rrRet impl hap R hclr hmv hmk hSN hserv ret hret b L g sp n mp mc t rp rl rc xp xc yp ylen Y yi
    zp zc zzp zzc st n0 M r18 r29 f29 he (CallW.CEnv.mono hce hK (Nat.le_refl _)) hn hn128 hmc hmc' ht hm hx r1016 r1024
    r1032 r224 r128 r904 r328 r320
    (fun p => ⟨hserv.2.2.1 _ _ (by omega), hserv.2.1 _ _ _ (by omega)⟩) hyl hyl' hy hY hyi hyi0 hzc
    (fun h => ⟨(hz h).1, (hz h).2.1⟩) hsv hzz hzz8 hzzm hzzy hzz4 hzzs (fr _ _ hzzU) hro hty r952 r936 r168 r400 r1000 r992
    (fun _ => hserv.1 _ _ _ (by omega)) (fun p d => hserv.2.1 _ _ _ (by omega)) (w16 _ _ hmO.2.1) hnm
    (by rw [hmV]; exact hkk) (by rw [hmV]; exact hmB) hfe hsth (w4 _ _ hstw) hsok (by omega) hcap (frl _ _ hug)
    (fun h => ⟨w4 _ _ (harr h).1, (harr h).2⟩) (frl _ _ (w4 _ _ huw)) hslen hwba hstwb (fr _ _ hsu)
    hmO.2.2.1 (fr _ _ hmO.2.2.2.1) hxO.2.2.1 (fr _ _ hxO.2.2.2.1) hyO.2.2.1 (fr _ _ hyO.2.2.2.1) hbud r960
    (fun _ => hserv.1 _ _ _ (by omega)) hinv hrl0 hrln hrc hrp hra hr48 hrh hrw hrS hrF hzr hzzx hzz0 S hpc hsp h3 h4 h5
    h18 h28 h29 hmem) ?_
  refine isReturn_mono fun s' h => ?_
  rw [hmV, hxv] at h
  exact h

end FvModexp.Arm64.W4Pro
