import FvModexp.Proofs.Arm64.Exp.W4PowAll
import FvModexp.Proofs.Arm64.Exp.W4Mid2

/-!
# window-4 (arm64): from the return of `stk.nat(17n)` (`p01`) to the return of the function

`W4PowAll.p01pow` (the table `powers[0..16)`, `p01 → j4`) then `W4Mid2.j4Ret` (`j4 → RET`). Every fact `j4Ret` needs
at `j4` is moved from the memory at `p01` through the table's frame `R.rt ++ tw sp bp n` (no allocation: `L` is
unchanged) — objects apart from the window `[sp-4288, sp+1040)` and from the table buffer `buf = bp[0:17n]` keep
their bytes, and slots outside `qw`/`pw` keep theirs.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step)

theorem apart_ent {a k bp n d : Nat} (h : Apart a k bp (8 * (17 * n))) (hd : d < 16) :
    Apart a k (bp + 8 * (d * n)) (8 * n) := by
  have e1 : d * n + n ≤ 17 * n := by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ 17 by omega); rw [Nat.add_mul] at this; omega
  unfold Apart at h ⊢; omega

theorem inp_buf {R : RtInv} {L : List (Nat × Nat)} {sp n bp d : Nat} {M : Memory}
    (hba : M.accessible bp (8 * (17 * n)) true = true) (hbb : bp + 8 * (17 * n) ≤ 2 ^ 48)
    (hbh : InRanges bp (8 * (17 * n)) L ∨ Outside bp (8 * (17 * n)) R.rt)
    (hbw : Apart bp (8 * (17 * n)) (sp - 4288) (4288 + 1040)) (hd : d < 16) :
    Inp R L sp n M (bp + 8 * (d * n)) := by
  have e1 : d * n + n ≤ 17 * n := by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ 17 by omega); rw [Nat.add_mul] at this; omega
  refine ⟨M.accessible_sub hba (Or.inr rfl) (by omega) (by omega), by omega,
    hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_⟩
  unfold Apart at hbw ⊢; omega

/-- `p01 → j4` frame: a held object apart from the window and from `buf` keeps its bytes -/
theorem trd {R : RtInv} {L : List (Nat × Nat)} {sp n bp a k : Nat} {M M' : Memory}
    (hF : MemFrame M M' (R.rt ++ tw sp bp n)) (hL : LiveFrame M M' L [(bp, bp + 8 * (17 * n))])
    (hh : InRanges a k L ∨ Outside a k R.rt) (h1 : Apart a k (sp - 4288) (4288 + 1040))
    (h2 : Apart a k bp (8 * (17 * n))) : M'.readLE a k = M.readLE a k := by
  have hF' : MemFrame M M' (R.rt ++ (qw sp ++ pw sp) ++ [(bp, bp + 8 * (17 * n))]) := by
    simp only [tw, List.append_assoc] at hF ⊢; exact hF
  unfold Apart at h1 h2
  exact FvModexp.Expmc.held_readLE hh hF' hL
    (by simp only [qw, pw, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)

/-- `p01 → j4` frame: a frame slot outside `qw`/`pw` keeps its word -/
theorem tslot {R : RtInv} {sp n bp K : Nat} {M M' : Memory}
    (hF : MemFrame M M' (R.rt ++ tw sp bp n)) (hrt : Outside (sp - 4288) (4288 + 1040) R.rt)
    (hbw : Apart bp (8 * (17 * n)) (sp - 4288) (4288 + 1040)) (h0 : 4288 ≤ sp)
    (hK : 120 ≤ K ∧ K + 8 ≤ 224 ∨ 232 ≤ K ∧ K + 8 ≤ 248 ∨ 256 ≤ K ∧ K + 8 ≤ 312 ∨ K = 336 ∨ K = 344 ∨ K = 352 ∨
      K = 360 ∨ K = 368 ∨ K = 376 ∨ K = 384 ∨ K = 392 ∨ K = 400 ∨ K = 408 ∨ K = 416 ∨ K = 424 ∨
      816 ≤ K ∧ K + 8 ≤ 824 ∨ 832 ≤ K ∧ K + 8 ≤ 880 ∨ 888 ≤ K ∧ K + 8 ≤ 1040) :
    M'.readLE (sp + K) 8 = M.readLE (sp + K) 8 := by
  refine hF.readLE _ _ ?_
  have hro : Outside (sp + K) 8 R.rt := hrt.of_sub (by omega) (by omega)
  unfold Apart at hbw
  simp only [tw, qw, pw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 from the return of `stk.nat(17n)` (`p01`) to the return -/
theorem p01Ret (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t bp onep rrp rrc xp xc yp ylen Y yi zp zc zzp zzc st n0 : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64)
    (he : Env R L g sp M) (hce : CallW.CEnv R L g sp 4304 1040 M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp)
    (hba : M.accessible bp (8 * (17 * n)) true = true) (hbb : bp + 8 * (17 * n) ≤ 2 ^ 48)
    (hbh : InRanges bp (8 * (17 * n)) L ∨ Outside bp (8 * (17 * n)) R.rt)
    (hbw : Apart bp (8 * (17 * n)) (sp - 4288) (4288 + 1040)) (hbg : Apart (g + 16) 8 bp (8 * (17 * n)))
    (hbm : Apart bp (8 * (17 * n)) mp (8 * n))
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * (17 * n)) onep (8 * n)) (hone1 : M.readLE onep (8 * n) = 1)
    (hrr : Inp R L sp n M rrp) (hbR : Apart bp (8 * (17 * n)) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * (17 * n)) xp (8 * n))
    (r1016 : M.readLE (sp + 1016) 8 = mp) (r1024 : M.readLE (sp + 1024) 8 = n) (r1032 : M.readLE (sp + 1032) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n) (r816 : M.readLE (sp + 816) 8 = onep)
    (r832 : M.readLE (sp + 832) 8 = rrp) (r256 : M.readLE (sp + 256) 8 = n) (r264 : M.readLE (sp + 264) 8 = rrc)
    (r904 : M.readLE (sp + 904) 8 = xp) (r328 : M.readLE (sp + 328) 8 = n) (r320 : M.readLE (sp + 320) 8 = xc)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    -- facts for `j4 → RET`
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hy : Inp R L sp ylen M yp) (hyb : Apart yp (8 * ylen) bp (8 * (17 * n))) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0)
    (hold : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) bp (8 * (17 * n)) ∧
      Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) onep (8 * n) ∧ Apart zp (8 * zc) st 24)
    (hzz : Buf R L g sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzzb : Apart zzp (8 * zzc) bp (8 * (17 * n))) (hzz4 : Apart zzp (8 * zzc) (sp - 4304) 16)
    (hzzo : Apart zzp (8 * zzc) onep (8 * n)) (hzzs : Apart zzp (8 * zzc) st 24)
    (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r952 : M.readLE (sp + 952) 8 = zc) (r936 : M.readLE (sp + 936) 8 = zp)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (hokm : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b)
    (hokM : ∀ p d, R.ok (Extracted.program.contractAddr "runtime.memmove") [p, d, 8 * n])
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm : NatNorm M mp n)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 1040)) (hstb : Apart st 24 bp (8 * (17 * n)))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 p01) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 (17 * n))
    (h2 : S.regs 2 = BitVec.ofNat 64 (17 * n))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibExp.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (Mj M' : Memory) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
        MemFrame M Mj (R.rt ++ tw sp bp n) ∧ LiveFrame M Mj L [(bp, bp + 8 * (17 * n))] ∧
        R.inv b L g (view R.rt L Mj) ∧ Mj.regions = M.regions ∧
        ZPost R L L' b b' g sp n Mj M' zp zc zp' zc' ∧
        ZjPost R b' L' g sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) yp ylen bp zp' zc'
          (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)))
          (zjVal n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64)
            (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)))
            Y ylen yi) st n0 onep r18 r29 M' s')) := by
  refine p01pow impl hap R hclr hmv ret hret _ b L g sp n mp mc t bp onep rrp rrc xp xc M r18 f29 he hn hn16 hmc
    hmc' ht hm hba hbb hbh hbw hbg hbm hone hbo hone1 hrr hbR hx hbx r1016 r1024 r1032 r224 r128 r816 r832 r256 r264
    r904 r328 r320 hok hinv S hpc hsp h0 h1 h2 h18 h28 h29 hmem ?_
  intro S' Mj c1 c2 c3 c4 c5 c6 hF hL hinvj hrgj m224 hE
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hwacc4 := hce.2.2.2.1
  have u1 := hbw; have u2 := hbg
  unfold Apart at u1 u2
  have rs := fun K hK => tslot (K := K) hF hwrt hbw hsp1 hK
  -- environment
  have hgo : Outside (g + 16) 8 (tw sp bp n) := by
    unfold Apart at hgw
    simp only [tw, qw, pw, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  have hws : ∀ r ∈ tw sp bp n, r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [tw, qw, pw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact M.accessible_sub hwacc4 (Or.inr rfl) (by simp only; omega) (by simp only; omega)
      | exact M.accessible_sub hba (Or.inr rfl) (by simp only; omega) (by simp only; omega)
  have he' : Env R L g sp Mj := env_frame he hF hgo
  have hce' : CallW.CEnv R L g sp 4304 1040 Mj := CallW.CEnv.frame hce hF hrgj hws hgo
  have hd' : Extracted.program.DataLoaded Mj := hce'.2.2.2.2.2.2.2.2.2.2.2.1
  -- objects
  have hm' := inp_frame hm hF
  have hmr : Mj.readLE mp (8 * n) = M.readLE mp (8 * n) :=
    trd hF hL hm.2.2.1 hm.2.2.2 (by have := hbm; unfold Apart at this ⊢; omega)
  have hy' := inp_frame hy hF
  have hYr : Mj.readLE yp (8 * ylen) = Y := by rw [trd hF hL hy.2.2.1 hy.2.2.2 hyb]; exact hY
  have hyi' : Mj.readLE (yp + 8 * (ylen - 1)) 8 = yi := by
    have hy4 := hy.2.2.2; have hyb' := hyb
    unfold Apart at hy4 hyb'
    rw [trd hF hL ?_ (by unfold Apart; omega) (by unfold Apart; omega)]
    · exact hyi
    · rcases hy.2.2.1 with h1 | h1
      · exact Or.inl (h1.sub (by omega) (by omega))
      · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hz' : 2 * n ≤ zc → Buf R L g sp n Mj zp zc ∧ zp % 8 = 0 := fun h =>
    ⟨buf_frame (hz h).1 hF, (hz h).2⟩
  have hold' : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ (∀ d, d < 16 → Apart zp (8 * zc) (bp + 8 * (d * n)) (8 * n)) ∧
      Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) onep (8 * n) ∧ Apart zp (8 * zc) st 24 := by
    intro h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hold h
    exact ⟨a1, a2, a3, fun d hd => apart_ent a4 hd, a5, a6, a7⟩
  have hbuf : ∀ d, d < 16 → Inp R L sp n Mj (bp + 8 * (d * n)) := fun d hd =>
    inp_buf (M := Mj) (by rw [hF.accessible]; exact hba) hbb hbh hbw hd
  have hone' : OneIn R L sp n Mj onep := by
    rcases hone with h | h
    · exact Or.inl (inp_frame h hF)
    · exact Or.inr h
  have hone1' : Mj.readLE onep (8 * n) = 1 := by
    rcases hone with h | ⟨rfl, h4⟩
    · rw [trd hF hL h.2.2.1 h.2.2.2 (by have := hbo; unfold Apart at this ⊢; omega)]; exact hone1
    · have : Mj.readLE (sp + 336) (8 * n) = M.readLE (sp + 336) (8 * n) := by
        refine hF.readLE _ _ ?_
        have hro : Outside (sp + 336) (8 * n) R.rt := hwrt.of_sub (by omega) (by omega)
        simp only [tw, qw, pw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
        omega
      rw [this]; exact hone1
  have hnm' : NatNorm Mj mp n := by
    rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2; have hbm' := hbm
      unfold Apart at hm4 hbm'
      rw [trd hF hL ?_ (by unfold Apart; omega) (by unfold Apart; omega)]
      · exact h
      · rcases hm.2.2.1 with h1 | h1
        · exact Or.inl (h1.sub (by omega) (by omega))
        · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hfe' : FinEnv sp g st n0 r29 ret Mj := by
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hfe
    have hgr : Mj.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
      hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hgo⟩)
    have hstw := hstw4; have hstb' := hstb
    unfold Apart at hstw hstb'
    have rsp : Mj.readLE sp 8 = M.readLE sp 8 := by
      refine hF.readLE _ _ ?_
      have hro : Outside sp 8 R.rt := hwrt.of_sub (by omega) (by omega)
      simp only [tw, qw, pw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
      omega
    have rsp8 : Mj.readLE (sp - 8) 8 = M.readLE (sp - 8) 8 := by
      refine hF.readLE _ _ ?_
      have hro : Outside (sp - 8) 8 R.rt := hwrt.of_sub (by omega) (by omega)
      simp only [tw, qw, pw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
      omega
    refine ⟨f1, f2, f3, by rw [hF.accessible]; exact f4, f5, by rw [hF.accessible]; exact f6, by rw [hgr]; exact f7, f8,
      by rw [rs 912 (by omega)]; exact f9, by rw [rs 840 (by omega)]; exact f10, by rw [rs 848 (by omega)]; exact f11,
      by rw [rs 856 (by omega)]; exact f12, f13, by rw [hF.accessible]; exact f14, ?_, f16, f17,
      by rw [rsp8]; exact f18, by rw [rsp]; exact f19⟩
    rw [trd hF hL (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (by unfold Apart; omega) (by unfold Apart; omega)]; exact f15
  refine reaches_mono (j4Ret impl hap R hclr hmv hmk hserv ret hret b L g sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) yp ylen Y
    yi bp zp zc zzp zzc
    (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)))
    Mj r18 r29 f29 onep st n0 he' hce' hn hn16 hmc hmc' (Nat.mod_lt _ (by decide)) hyl hyl' hm' hy' hYr hyi' hyi0 hzc
    hz' hold' (buf_frame hzz hF) hzz8 hzzm hzzy (fun d hd => apart_ent hzzb hd) hzz4 hzzo hzzs hE hbuf hd' hro hty
    (by rw [rs 952 (by omega)]; exact r952) (by rw [rs 936 (by omega)]; exact r936)
    (by rw [rs 128 (by omega)]; exact r128) (by rw [rs 168 (by omega)]; exact r168)
    (by rw [rs 400 (by omega)]; exact r400) (by rw [rs 1000 (by omega)]; exact r1000)
    (by rw [rs 992 (by omega)]; exact r992) (by rw [rs 1024 (by omega)]; exact r1024) m224
    (by rw [rs 1016 (by omega)]; exact r1016) (by rw [rs 1032 (by omega)]; exact r1032)
    hokm hok hokM hinvj hmw4 hnm' hone' hone1' (by rw [rs 816 (by omega)]; exact r816)
    (by rw [hmr]; exact hkk) (by rw [hmr]; exact hmB) hfe' hsth hstw4 S' c1 c2 c3 c4 c5 c6) ?_
  exact isReturn_mono fun s ⟨M', zp', zc', L', b', hZ, hJ⟩ =>
    ⟨Mj, M', zp', zc', L', b', hF, hL, hinvj, hrgj, hZ, by rw [hmr] at hJ; exact hJ⟩

end FvModexp.Arm64.W4Pro
