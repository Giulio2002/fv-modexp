import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Mid
import FvModexp.Proofs.Arm64.Exp.W2Zm

/-!
# window-2 (arm64): from the end of the table (`j4`) to the return

`zmake` (`z = z.make(2n)`, reuse or `makeslice`) → `zjRet`. The facts `zjRet` needs at `zj` are moved from the
memory at `j4` through `ZPost` (frame `R.rt ++ [(sp-4096, sp-8), (sp+8, sp+152)]`, `LiveExt L L'`); the buffer
facts of the new `z` come from `bufs_of` (old array: the caller's facts; fresh: `InRanges R.rt ∧ ApartAll L`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step)

theorem apart_held {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart p k a n := by
  rcases hh with h | h
  · exact hap.apart_of_inRanges h
  · have := out_inR h hin; unfold Apart; omega

/-- the loop buffers after `z = z.make(2n)`: the old array (caller's facts) or a fresh one -/
theorem bufs_of {R : RtInv} {L L' : List (Nat × Nat)} {g sp n mp yp ylen zp zc zp' zc' zzp zzc onep st : Nat}
    {pp : Nat → Nat} {M : Memory}
    (hz' : Buf R L' g sp n M zp' zc') (hz8 : zp' % 8 = 0) (hzz : Buf R L' g sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hor : (zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L))
    (hold : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ (∀ d, d < 4 → Apart zp (8 * zc) (pp d) (8 * n)) ∧
      Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) onep (8 * n) ∧ Apart zp (8 * zc) st 24)
    (hwr : Outside (sp - 4304) 16 R.rt)
    (hzzh : InRanges zzp (8 * zzc) L ∨ Outside zzp (8 * zzc) R.rt)
    (hmh : InRanges mp (8 * n) L ∨ Outside mp (8 * n) R.rt) (hyh : InRanges yp (8 * ylen) L ∨ Outside yp (8 * ylen) R.rt)
    (hph : ∀ d, d < 4 → InRanges (pp d) (8 * n) L ∨ Outside (pp d) (8 * n) R.rt)
    (hoh : InRanges onep (8 * n) L ∨ Outside onep (8 * n) R.rt) (hsh : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzzp : ∀ d, d < 4 → Apart zzp (8 * zzc) (pp d) (8 * n)) (hzz4 : Apart zzp (8 * zzc) (sp - 4304) 16)
    (hzzo : Apart zzp (8 * zzc) onep (8 * n)) (hzzs : Apart zzp (8 * zzc) st 24) :
    Bufs R L' g sp n mp yp ylen pp [(onep, 8 * n), (st, 24)] M zp' zc' zzp zzc := by
  have ext2 : ∀ (P : Nat → Nat → Prop), P onep (8 * n) → P st 24 → ∀ q ∈ [(onep, 8 * n), (st, 24)], P q.1 q.2 := by
    intro P h1 h2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact h1
    · exact h2
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hold hz'.1
    exact ⟨hz', hzz, a1, a2, hzzm, a3, hzzy, fun d hd => ⟨a4 d hd, hzzp d hd⟩, hz8, hzz8, a5, hzz4,
      ext2 (fun a k => Apart zp' (8 * zc') a k ∧ Apart zzp (8 * zzc) a k) ⟨a6, hzzo⟩ ⟨a7, hzzs⟩⟩
  · have hw : Apart zp' (8 * zc') (sp - 4304) 16 := by
      have := out_inR hwr hin; unfold Apart; omega
    exact ⟨hz', hzz, apart_held hin hap hzzh, apart_held hin hap hmh, hzzm, apart_held hin hap hyh, hzzy,
      fun d hd => ⟨apart_held hin hap (hph d hd), hzzp d hd⟩, hz8, hzz8, hw, hzz4,
      ext2 (fun a k => Apart zp' (8 * zc') a k ∧ Apart zzp (8 * zzc) a k) ⟨apart_held hin hap hoh, hzzo⟩
        ⟨apart_held hin hap hsh, hzzs⟩⟩

theorem inp_ext {R : RtInv} {L L' : List (Nat × Nat)} {sp n p : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (hx : LiveExt R L L') (h : Inp R L sp n M p) (hf : MemFrame M M' ws) : Inp R L' sp n M' p :=
  ⟨by rw [hf.accessible]; exact h.1, h.2.1, hx.held h.2.2.1, h.2.2.2⟩

theorem buf_ext {R : RtInv} {L L' : List (Nat × Nat)} {g sp n p c : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (hx : LiveExt R L L') (h : Buf R L g sp n M p c) (hf : MemFrame M M' ws) : Buf R L' g sp n M' p c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨a1, a2, by rw [hf.accessible]; exact a3, a4, hx.held a5, a6, a7⟩

/-- the `ZPost` frame: held objects apart from the zmake window keep their bytes -/
theorem zrd {R : RtInv} {L : List (Nat × Nat)} {sp a k : Nat} {M M' : Memory}
    (hF : MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 152)])) (hL : LiveFrame M M' L [])
    (hh : InRanges a k L ∨ Outside a k R.rt) (h1 : Outside a k [(sp - 4096, sp - 8), (sp + 8, sp + 152)]) :
    M'.readLE a k = M.readLE a k := by
  rcases hh with h | h
  · exact hL.readLE a k h trivial
  · exact hF.readLE a k (by simp only [outside_append]; exact ⟨h, h1⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-2 from the end of the table (`j4`) to the return -/
theorem j4Ret (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y yi bp zp zc zzp zzc : Nat) (tbl : Nat → Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (onep st n0 : Nat)
    (he : Env R L g sp M) (hce : CallW.CEnv R L g sp 4304 752 M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hk0 : k0 < 2 ^ 64)
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hm : Inp R L sp n M mp) (hy : Inp R L sp ylen M yp) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0)
    (hold : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ (∀ d, d < 4 → Apart zp (8 * zc) (bp + 8 * (d * n)) (8 * n)) ∧
      Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) onep (8 * n) ∧ Apart zp (8 * zc) st 24)
    (hzz : Buf R L g sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzzp : ∀ d, d < 4 → Apart zzp (8 * zzc) (bp + 8 * (d * n)) (8 * n)) (hzz4 : Apart zzp (8 * zzc) (sp - 4304) 16)
    (hzzo : Apart zzp (8 * zzc) onep (8 * n)) (hzzs : Apart zzp (8 * zzc) st 24)
    (hent : ∀ d, d < 4 → Ent sp n bp tbl M d) (hbuf : ∀ d, d < 4 → Inp R L sp n M (bp + 8 * (d * n)))
    (hd : Extracted.program.DataLoaded M) (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r664 : M.readLE (sp + 664) 8 = zc) (r648 : M.readLE (sp + 648) 8 = zp) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r712 : M.readLE (sp + 712) 8 = ylen) (r704 : M.readLE (sp + 704) 8 = yp)
    (r736 : M.readLE (sp + 736) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r728 : M.readLE (sp + 728) 8 = mp)
    (r744 : M.readLE (sp + 744) 8 = mc)
    (hokm : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hokM : ∀ p d, R.ok (Extracted.program.contractAddr "runtime.memmove") [p, d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm : NatNorm M mp n)
    (hone : OneIn R L sp n M onep) (hone1 : M.readLE onep (8 * n) = 1) (r528 : M.readLE (sp + 528) 8 = onep)
    (hkk : (k0 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 752))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 j4) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (M' : Memory) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
        ZPost R L L' b b' g sp n M M' zp zc zp' zc' ∧
        ZjPost R b' L' g sp n mp mc k0 yp ylen bp zp' zc' zzp zzc tbl
          (zjVal n (M.readLE mp (8 * n)) k0 tbl Y ylen yi) st n0 onep r18 r29 M' s')) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmkL := MakesliceLiveContract.of_codeIn hc hmk
  refine zmake impl R hmkL ret hret _ b L g sp n zp zc M r18 f29 he hn hn16 hzc hz hd hro hty r664 r648 r736 r128
    hokm hinv S hpc hsp h18 h28 h29 hmem ?_
  intro S' M' zp' zc' L' b' hpc' hsp' h0' h13' h14' h18' h28' h29' hm' hZ
  have hZ0 := hZ
  obtain ⟨he', hz', hz8', hx, hb', hF, hL, hinv', hrg, hor⟩ := hZ0
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have rdo : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4288) (4288 + 752) →
      M'.readLE a k = M.readLE a k := by
    intro a k hh h1
    unfold Apart at h1
    exact zrd hF hL hh (by simp only [outside_cons, outside_nil, and_true]; omega)
  have rs : ∀ K, 152 ≤ K → K + 8 ≤ 752 → M'.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K k1 k2 =>
    zrd hF hL (Or.inr (hwrt.of_sub (by omega) (by omega))) (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hmr : M'.readLE mp (8 * n) = M.readLE mp (8 * n) := rdo _ _ hm.2.2.1 hm.2.2.2
  have hgo : Outside (g + 16) 8 [(sp - 4096, sp - 8), (sp + 8, sp + 152)] := by
    unfold Apart at hgw; simp only [outside_cons, outside_nil, and_true]; omega
  have hws : ∀ r ∈ [(sp - 4096, sp - 8), (sp + 8, sp + 152)], r.1 < r.2 →
      M.accessible r.1 (r.2 - r.1) true = true := by
    have hacc4 := hce.2.2.2.1
    intro r hr _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals exact M.accessible_sub hacc4 (Or.inr rfl) (by simp only; omega) (by simp only; omega)
  have hce1 := CallW.CEnv.frame hce hF hrg hws hgo
  have hce' : CallW.CEnv R L' g sp 4304 752 M' := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hce1
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hx.liveSep c11 ?_, c12, c13⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only; rw [show sp + 752 - (sp - 4304) = 4304 + 752 by omega]; exact c8
  have hent' : ∀ d, d < 4 → Ent sp n bp tbl M' d := by
    intro d hd
    obtain ⟨eE1, eE2, eE3, eE4⟩ := hent d hd
    have hbd := hbuf d hd
    refine ⟨by rw [rdo _ _ hbd.2.2.1 hbd.2.2.2]; exact eE1, ?_, ?_, ?_⟩
    · rw [show sp + 432 + 24 * d = sp + (432 + 24 * d) by omega, rs _ (by omega) (by omega), ← Nat.add_assoc]
      exact eE2
    · rw [show sp + 440 + 24 * d = sp + (440 + 24 * d) by omega, rs _ (by omega) (by omega), ← Nat.add_assoc]
      exact eE3
    · rw [show sp + 448 + 24 * d = sp + (448 + 24 * d) by omega, rs _ (by omega) (by omega), ← Nat.add_assoc]
      exact eE4
  have hzz' := buf_ext hx hzz hF
  have hwr4 : Outside (sp - 4304) 16 R.rt := hce.2.2.2.2.2.2.2.1.of_sub (by omega) (by omega)
  have hone' : OneIn R L' sp n M' onep := by
    rcases hone with h | h
    · exact Or.inl (inp_ext hx h hF)
    · exact Or.inr h
  have hoh : InRanges onep (8 * n) L ∨ Outside onep (8 * n) R.rt := by
    rcases hone with h | ⟨rfl, h4⟩
    · exact h.2.2.1
    · exact Or.inr (hwrt.of_sub (by omega) (by omega))
  have hB' := bufs_of (L := L) (L' := L') (zp := zp) (zc := zc) (pp := fun d => bp + 8 * (d * n)) hz' hz8' hzz'
    hzz8 hor hold hwr4 hzz.2.2.2.2.1 hm.2.2.1 hy.2.2.1 (fun d hd => (hbuf d hd).2.2.1) hoh hsth hzzm hzzy hzzp hzz4
    hzzo hzzs
  have hone1' : M'.readLE onep (8 * n) = 1 := by
    rcases hone with h | ⟨rfl, h4⟩
    · rw [rdo _ _ h.2.2.1 h.2.2.2]; exact hone1
    · rw [zrd hF hL (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hone1
  have hnm' : NatNorm M' mp n := by
    rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2
      unfold Apart at hm4
      rw [rdo _ _ ?_ (by unfold Apart; omega)]
      · exact h
      · rcases hm.2.2.1 with h1 | h1
        · exact Or.inl (h1.sub (by omega) (by omega))
        · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hfe' : FinEnv sp g st n0 r29 ret M' := by
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hfe
    have hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
      hF.readLE _ _ (by simp only [outside_append]; exact ⟨hgrt, hgo⟩)
    have hstw := hstw4
    unfold Apart at hstw
    refine ⟨f1, f2, f3, by rw [hF.accessible]; exact f4, f5, by rw [hF.accessible]; exact f6, by rw [hgr]; exact f7, f8,
      by rw [rs 624] <;> omega, by rw [rs 552] <;> omega, by rw [rs 560] <;> omega, by rw [rs 568] <;> omega, f13,
      by rw [hF.accessible]; exact f14, ?_, f16, f17, ?_, ?_⟩
    · rw [rdo _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
        (by unfold Apart; omega)]; exact f15
    · rw [zrd hF hL (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact f18
    · rw [zrd hF hL (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact f19
  have hyi' : M'.readLE (yp + 8 * (ylen - 1)) 8 = yi := by
    have hy4 := hy.2.2.2
    unfold Apart at hy4
    rw [rdo _ _ ?_ (by unfold Apart; omega)]
    · exact hyi
    · rcases hy.2.2.1 with h1 | h1
      · exact Or.inl (h1.sub (by omega) (by omega))
      · exact Or.inr (h1.of_sub (by omega) (by omega))
  refine reaches_mono (zjRet impl hap R hclr hmv hmk hserv ret hret b' L' g sp n mp mc k0 yp ylen Y yi bp zp' zc' zzp
    zzc tbl M' r18 r29 f29 onep st n0 he' hce' hn hn16 hmc hmc' hk0 hyl hyl' (inp_ext hx hm hF) (inp_ext hx hy hF)
    (by rw [rdo _ _ hy.2.2.1 hy.2.2.2]; exact hY) hyi' hyi0 hz' hzz' hent' (fun d hd => inp_ext hx (hbuf d hd) hF)
    hB' (by rw [rs 168 (by omega) (by omega)]; exact r168) (by rw [rs 400 (by omega) (by omega)]; exact r400)
    (by rw [rs 712 (by omega) (by omega)]; exact r712) (by rw [rs 704 (by omega) (by omega)]; exact r704)
    (by rw [rs 736 (by omega) (by omega)]; exact r736) (by rw [rs 224 (by omega) (by omega)]; exact r224)
    (by rw [rs 728 (by omega) (by omega)]; exact r728) (by rw [rs 744 (by omega) (by omega)]; exact r744)
    hokS (hokM zp') hinv' hmw4 hnm' hone' hone1' (by rw [rs 528 (by omega) (by omega)]; exact r528)
    (by rw [hmr]; exact hkk) (by rw [hmr]; exact hmB) hfe' (hsth.imp hx.inRanges_old id) hstw4
    S' hpc' hsp' h0' h13' h14' h18' h28' h29' hm') ?_
  exact isReturn_mono fun s h => ⟨M', zp', zc', L', b', hZ, by rw [hmr] at h; exact h⟩

end FvModexp.Arm64.W2Pro
