import FvModexp.Proofs.Amd64.Exp.W2Posts2
import FvModexp.Proofs.Amd64.Exp.W2PSpec

set_option autoImplicit false

/-!
# window-2 (amd64): from the return of `stk.nat(5n)` (`p01`) to the return of the function (agent expmc s49)

Twin of `Arm64.W2P01Ret.p01Ret`. `p01pow` (the table, `p01 → j4`) then `j4Ret` (`j4 → RET`). The facts `j4Ret`
needs at `j4` are moved from the memory `M` at `p01` along the table frame `FP` (no allocation, `L` unchanged): held
objects apart from the frame and from `buf` keep their bytes (`FP.read`), frame words outside `pw` keep theirs
(`FP.slot`). `PreT` = `Pre4` without the table (which only exists from `j4` on) and without `k0` (written at `0xd8`
by the table code).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs InpC Inp.c OneIn FinEnv)

theorem apart_ent {a k bp bc n d : Nat} (h : Apart a k bp (8 * bc)) (hbc : 5 * n ≤ bc) (hd : d < 4) :
    Apart a k (bp + 8 * (d * n)) (8 * n) := by
  have e1 : d * n + n ≤ 5 * n := by
    have := Nat.mul_le_mul_right n (show d + 1 ≤ 5 by omega); rw [Nat.add_mul] at this; omega
  unfold Apart at h ⊢; omega

theorem OldB.a {n mp yp ylen onep st bp bc p c : Nat} (h : OldB n mp yp ylen onep st bp bc p c) (hbc : 5 * n ≤ bc) :
    OldA n mp yp ylen onep st (tp bp n) p c :=
  ⟨h.1, h.2.1, fun _ hd => apart_ent h.2.2.1 hbc hd, h.2.2.2.1, h.2.2.2.2⟩

/-- a held object outside the written frame words and apart from `buf` reads as at the anchor -/
theorem FP.read' {R : RtInv} {L : List (Nat × Nat)} {sp bp bc : Nat} {M0 M : Memory} {a k : Nat}
    (h : FP R L sp bp bc M0 M) (hh : InRanges a k L ∨ Outside a k R.rt) (h1 : Outside a k (pw sp))
    (h2 : Apart a k bp (8 * bc)) : M.readLE a k = M0.readLE a k := by
  unfold Apart at h2
  exact FvModexp.Expmc.held_readLE hh h.1 h.2 h1 (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
/-- `Pre4` at `j4` from `PreT` at `p01`, the table frame and the table -/
theorem PreT.pre4 {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 bp bc yp ylen Y yi Mv onep st n0 fbp r : Nat}
    {tbl : Nat → Nat} {M M' : Memory} (h : PreT R L sp n mp mc yp ylen Y yi Mv onep st n0 fbp r M)
    (hs : PStatic R L g fs sp n mp mc k0 bp bc M) (hF : FP R L sp bp bc M M') (hrg : M'.regions = M.regions)
    (hro : RoOut R) (hsl : PSl sp n mp mc k0 bp bc M') (hE : ∀ d, d < 4 → Ent sp n (tp bp n) (tc n) tbl M' d)
    (hby : Apart yp (8 * ylen) bp (8 * bc)) (hbo : Apart bp (8 * bc) onep (8 * n)) (hbs : Apart st 24 bp (8 * bc))
    (hyl : 0 < ylen) :
    Pre4 R L sp n mp mc k0 yp ylen Y yi Mv (tp bp n) tbl onep st n0 fbp r M' := by
  obtain ⟨hd, hm, hy, hY, hyi, s1, s2, s3, s5, s6, hnm, hmv, hone, hone1, r328, hfe, hsth⟩ := h
  have he := hs.1
  have hs1 : 4296 ≤ sp := he.2.1
  have hs2 : sp + 0x2a8 ≤ 2 ^ 48 := he.2.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt := he.2.2.2.2.2.2.2.1
  have hbc := hs.2.2.2.2.2.2.2.1
  have hbm := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hn : 0 < n := hs.2.1
  have hbw := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hba := hs.2.2.2.2.2.2.2.2.2.1
  have hwacc := he.2.2.2.1
  have rs : ∀ K, 0x60 ≤ K → K + 8 ≤ 0x2a8 → Outside (sp + K) 8 (pw sp) → M'.readLE (sp + K) 8 = M.readLE (sp + K) 8 :=
    fun K k1 k2 k3 => FP.slot hs hF k1 k2 k3
  have hws : ∀ q ∈ pw sp ++ [(bp, bp + 8 * bc)], q.1 < q.2 → M.accessible q.1 (q.2 - q.1) true = true := by
    intro q hq _
    simp only [pw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals first
      | exact Arm64.Memory.accessible_sub (m := M) hwacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
      | exact Arm64.Memory.accessible_sub (m := M) hba (Or.inr rfl) (by simp only; omega) (by simp only; omega)
  have hF' : MemFrame M M' (R.rt ++ (pw sp ++ [(bp, bp + 8 * bc)])) := by rw [← List.append_assoc]; exact hF.1
  have inp : ∀ k p, Inp R L sp k M p → Inp R L sp k M' p := fun k p hp =>
    ⟨by rw [hF.1.accessible]; exact hp.1, hp.2⟩
  have rsub : ∀ a k p q, (InRanges p q L ∨ Outside p q R.rt) → Apart p q (sp - 4296) (4296 + 0x2a8) →
      Apart p q bp (8 * bc) → p ≤ a → a + k ≤ p + q → M'.readLE a k = M.readLE a k := by
    intro a k p q hh h1 h2 e1 e2
    refine FP.read hF (hh.imp (fun h => h.sub e1 e2) (fun h => h.of_sub e1 e2)) hs1 ?_ ?_
    · unfold Apart at h1 ⊢; omega
    · unfold Apart at h2 ⊢; omega
  refine ⟨FvModexp.dataLoaded_frame64 hd hrg hro hF' hws, inp _ _ hm, inp _ _ hy,
    by rw [FP.read hF hy.2.2.1 hs1 hy.2.2.2 hby]; exact hY, ?_, hE, fun d hd => inp _ _ (inp_ent hs (by omega)),
    by rw [rs 0x280 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact s1,
    by rw [rs 0x278 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact s2,
    hsl.1, hsl.2.2.2.1, hsl.2.1, hsl.2.2.1, ?_, by rw [FP.read hF hm.2.2.1 hs1 hm.2.2.2 (by unfold Apart at hbm ⊢; omega)]; exact hmv,
    ?_, ?_, by rw [rs 0x210 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact r328,
    ?_, hsth⟩
  · have hyw := hy.2.2.2
    unfold Apart at hyw
    rw [rsub _ _ _ _ hy.2.2.1 hy.2.2.2 hby (by omega) (by omega)]; exact hyi
  · rcases hnm with h | h
    · exact Or.inl h
    · right
      rw [rsub _ _ _ _ hm.2.2.1 hm.2.2.2 (by unfold Apart at hbm ⊢; omega) (by omega) (by omega)]; exact h
  · rcases hone with h | h
    · exact Or.inl (inp _ _ h)
    · exact Or.inr h
  · rcases hone with h | ⟨rfl, h4⟩
    · rw [FP.read hF h.2.2.1 hs1 h.2.2.2 hbo.symm]; exact hone1
    · rw [FP.read' hF (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [pw, outside_cons, outside_nil, and_true]; omega) hbo.symm]; exact hone1
  · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
    have hstw := f12
    unfold Apart at hstw
    refine ⟨f1, f2, f3, by rw [hF.1.accessible]; exact f4,
      by rw [rs 0x260 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact f5,
      by rw [rs 0x228 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact f6,
      by rw [rs 0x230 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact f7,
      by rw [rs 0x238 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact f8,
      f9, by rw [hF.1.accessible]; exact f10, ?_, f12,
      by rw [rs 0x268 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact f13,
      by rw [rs 0x270 (by omega) (by omega) (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact f14,
      f15⟩
    rw [rsub _ _ _ _ hsth f12 hbs (by omega) (by omega)]; exact f11

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-2 (amd64) from the return of `stk.nat(5n)` (`p01`) to the return -/
theorem p01Ret (hJ4 : FvModexp.Amd64.W2Pro.J4Spec) (hP01 : FvModexp.Amd64.W2Pro.P01Spec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc t bp bc onep rrp rrc xp yp ylen Y yi Mv : Nat}
    {zp zc zzp zzc st n0 fbp r : Nat} {M : Memory} {r5 : W64}
    (hs : PStatic R L g fs sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc M) (ht : t < 2 ^ 64)
    (hP : PreT R L sp n mp mc yp ylen Y yi Mv onep st n0 fbp r M)
    (hbo : Apart bp (8 * bc) onep (8 * n)) (hrr : Inp R L sp n M rrp) (hbr : Apart bp (8 * bc) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * bc) xp (8 * n))
    (hby : Apart yp (8 * ylen) bp (8 * bc)) (hbs : Apart st 24 bp (8 * bc))
    (s78 : M.readLE (sp + 0x78) 8 = 2 * n) (sd8 : M.readLE (sp + 0xd8) 8 = t)
    (s338 : M.readLE (sp + 0x220) 8 = rrp) (sf8 : M.readLE (sp + 0xf8) 8 = n) (s100 : M.readLE (sp + 0x100) 8 = rrc)
    (s370 : M.readLE (sp + 0x258) 8 = xp) (s138 : M.readLE (sp + 0x140) 8 = n)
    (hinv : R.inv b L g (view R.rt L M))
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g fs sp n M zp zc ∧ zp % 8 = 0)
    (hzzc : zzc < 2 ^ 40) (hzz : 2 * n ≤ zzc → Buf R L g fs sp n M zzp zzc ∧ zzp % 8 = 0)
    (hoz : 2 * n ≤ zc → OldB n mp yp ylen onep st bp bc zp zc)
    (hozz : 2 * n ≤ zzc → OldB n mp yp ylen onep st bp bc zzp zzc)
    (hzzz : 2 * n ≤ zc → 2 * n ≤ zzc → Apart zp (8 * zc) zzp (8 * zzc))
    (r3d0 : M.readLE (sp + 0x2b8) 8 = zc) (r3c0 : M.readLE (sp + 0x2a8) 8 = zp)
    (ra0 : M.readLE (sp + 0xa0) 8 = zzc) (r188 : M.readLE (sp + 0x190) 8 = zzp)
    (hacc2 : M.accessible (sp + 0x2a8) 0x20 false = true) (hca : Outside (sp + 0x2a8) 0x20 R.rt)
    (hcb : Apart (sp + 0x2a8) 0x20 bp (8 * bc))
    (hokm : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4])
    (hb1 : zc < 2 * n → blockSize (8 * (2 * n + 4)) true ≤ b)
    (hb2 : zzc < 2 * n → 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hfbp : fbp < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 p01) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 bc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ Mj : Memory, FP R L sp bp bc M Mj ∧ R.inv b L g (view R.rt L Mj) ∧ Mj.regions = M.regions ∧
        J4Post R b L g fs sp n mp yp ylen zp zc zzp zzc ((2 ^ 64 - t) % 2 ^ 64) (tp bp n)
          (zjVal n Mv ((2 ^ 64 - t) % 2 ^ 64) (Exp.montPow n Mv ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n))
            (M.readLE rrp (8 * n))) Y ylen yi) st n0 onep fbp Mj s') := by
  have hP0 := hP
  obtain ⟨-, -, -, -, -, -, -, s3a8, s3b0, s3b8, -, hmv', hone, hone1, s328, -, -⟩ := hP0
  have he := hs.1
  have hs1 : 4296 ≤ sp := he.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt := he.2.2.2.2.2.2.2.1
  have hbc := hs.2.2.2.2.2.2.2.1
  have hbw := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbg := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbf := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine hP01 hap hclr hmv hs ht hone hbo hone1 hrr hbr hx hbx s78 s3b0 s3a8 s3b8 sd8 s328 s338 sf8 s100 s370 s138
    hinv S hpc hsp hmem h0 h1 h5 h14 hfs hx15 hdf ?_
  intro Sj c1 c2 c3 c4 c5 c6 c7 hF hinvj hrgj hslj hE
  have rs : ∀ K, 0x60 ≤ K → K + 8 ≤ 0x2a8 → Outside (sp + K) 8 (pw sp) →
      Sj.mem.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K k1 k2 k3 => FP.slot hs hF k1 k2 k3
  have hF' : MemFrame M Sj.mem (R.rt ++ (pw sp ++ [(bp, bp + 8 * bc)])) := by rw [← List.append_assoc]; exact hF.1
  have u1 := hbg; have u2 := hbf; have u3 := he.2.2.2.2.2.2.2.2.1; have u4 := he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at u1 u2 u3 u4
  have hgo : Outside (g + 16) 8 (pw sp ++ [(bp, bp + 8 * bc)]) := by
    simp only [pw, outside_append, outside_cons, outside_nil, and_true]; omega
  have hfo : Outside (fs - 8) 8 (pw sp ++ [(bp, bp + 8 * bc)]) := by
    simp only [pw, outside_append, outside_cons, outside_nil, and_true]; omega
  have hej : Env R L g fs sp Sj.mem := Env.frame he hF' hgo hfo (LiveExt.refl R L)
  have hPj := PreT.pre4 hP hs hF hrgj hro hslj hE hby hbo hbs hyl
  have hsl3 : ∀ K, 0x60 ≤ K → K + 8 ≤ 0x2a8 → (K + 8 ≤ 0xd8 ∨ 0xe0 ≤ K) → (K + 8 ≤ 0xf0 ∨ 0xf8 ≤ K) →
      (K + 8 ≤ 0x140 ∨ 0x150 ≤ K) → (K + 8 ≤ 0x1b0 ∨ 0x210 ≤ K) → (K + 8 ≤ 0x218 ∨ 0x220 ≤ K) →
      Sj.mem.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K k1 k2 k3 k4 k5 k6 k7 =>
    rs K k1 k2 (by simp only [pw, outside_cons, outside_nil, and_true]; omega)
  have hca0 : ∀ K, K + 8 ≤ 0x20 → Sj.mem.readLE (sp + 0x2a8 + K) 8 = M.readLE (sp + 0x2a8 + K) 8 := by
    intro K hK
    have u5 := hcb; unfold Apart at u5
    refine hF.1.readLE _ _ ?_
    simp only [pl, pw, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hca.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  refine ReachesRet.mono (hJ4 hap hclr hmv hmk hmvok hwt hro hej hPj (hs.2.1) (hs.2.2.1) (hs.2.2.2.1)
    (hs.2.2.2.2.1) (hs.2.2.2.2.2.1) hyl hyl' hyi0 hzc
    (fun h => ⟨buf_frame (hz h).1 hF.1, (hz h).2⟩) hzzc (fun h => ⟨buf_frame (hzz h).1 hF.1, (hzz h).2⟩)
    (fun h => (hoz h).a hbc) (fun h => (hozz h).a hbc) hzzz
    (by rw [hca0 0x10 (by omega)]; exact r3d0) (by rw [hca0 0 (by omega)]; exact r3c0)
    (by rw [hsl3 0x78 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s78)
    (by rw [hsl3 0xa0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact ra0)
    (by rw [hsl3 0x190 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r188)
    (by rw [hF.1.accessible]; exact hacc2) hokm hb1 hb2 (hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hinvj hkk hmB hfbp
    Sj c1 c2 rfl c3 c4 c5 c6 c7) ?_
  intro s h
  rw [hmv'] at h
  exact ⟨Sj.mem, hF, hinvj, hrgj, h⟩

end FvModexp.Amd64.W2Pro
