import FvModexp.Proofs.Amd64.Exp.W4Posts2
import FvModexp.Proofs.Amd64.Exp.W4Loop
import FvModexp.Proofs.Amd64.Exp.W4Tail
import FvModexp.Proofs.Amd64.Exp.W4ZcA
import FvModexp.Proofs.Amd64.Exp.W4ZmDefs

set_option autoImplicit false

/-!
# window-4 (amd64): from the join after `z.make`/`zz.make` (`zj`) to the return (agent expmc s48)

Twin of `Arm64.W4Mid.zjRet`. `zcopy` (first window) → anchor `M0` = memory at the loop test → `W4Loop.loop` →
`W4Tail.exitRet`. The conclusion packages the anchor and the exit buffers (`ZjPost`); the function theorem composes
the frames. The loop's buffer predicate `Pz` carries which buffer is which and the 8-alignment of both.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 (amd64) from `zj` (after `z.make(2n)`, `zz.make(2n)`) to the return -/
theorem zjRet {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp mc k0 yp ylen Y yi zp zc zzp zzc : Nat) (pp tbl : Nat → Nat)
    (M : Memory) (r5 : W64) (onep st n0 bp r : Nat)
    (he : Env R L g fs sp M) (hd : Extracted.program.DataLoaded M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hk0 : k0 < 2 ^ 64)
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hm : Inp R L sp n M mp) (hy : Inp R L sp ylen M yp) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hz : Buf R L g fs sp n M zp zc) (hzz : Buf R L g fs sp n M zzp zzc) (hz8 : zp % 8 = 0) (hzz8 : zzp % 8 = 0)
    (hent : ∀ d, d < 16 → Ent sp n pp (fun _ => 2 * n) tbl M d) (hbuf : ∀ d, d < 16 → Inp R L sp n M (pp d))
    (hB : Bufs R L g fs sp n mp yp ylen pp [(onep, 8 * n), (st, 24)] M zp zc zzp zzc)
    (r398 : M.readLE (sp + 0x398) 8 = ylen) (r390 : M.readLE (sp + 0x390) 8 = yp)
    (r168 : M.readLE (sp + 0x168) 8 = zp) (r88 : M.readLE (sp + 0x88) 8 = zc)
    (r3a8 : M.readLE (sp + 0x3a8) 8 = mp) (rd8 : M.readLE (sp + 0xd8) 8 = k0) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (r3b8 : M.readLE (sp + 0x3b8) 8 = mc)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])
    (hinv : R.inv b L g (view R.rt L M)) (hnm : NatNorm M mp n)
    (hone : OneIn R L sp n M onep) (hone1 : M.readLE onep (8 * n) = 1) (r328 : M.readLE (sp + 0x328) 8 = onep)
    (hkk : (k0 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp st n0 bp r M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt) (hbp : bp < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 zj) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h1 : S.regs 1 = BitVec.ofNat 64 zzp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (ZjPost R b L g fs sp n mp yp ylen zp zc zzp zzc k0 pp (zjVal n (M.readLE mp (8 * n)) k0 tbl Y ylen yi)
        st n0 onep bp M) := by
  have hc := codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive64.of_codeIn hc hmv
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hB0 := hB
  obtain ⟨-, -, hzzz, hzm, hzzm, hzy, hzzy, hzt, hzext⟩ := hB0
  have hz6 := hz.2.2.2.2.2.1
  unfold Apart at hz6
  have hzzp : zzp < 2 ^ 64 := by have := hzz.2.2.2.1; omega
  refine zcopy impl hmvL b L g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi pp (fun _ => 2 * n) tbl M r5 he hn hn16 hz
    (by have := hzz.1; omega) hzz.2.1 hzzp hy hyl hyl' hyi hyi0 hent hbuf (fun d hd => (hzt d hd).1) r398 r390 r168 r88
    r3a8 rd8 r3b0 r3b8 (fun d => hmvok _ _ _ (by omega)) hinv S hpc hsp hmem h5 h14 hfs hx15 hdf h0 h2 h1 h11 h12 ?_
  intro S' hpc' hsp' h5' h14' hfs' hx15' hdf' h0' h2' h8' h11' h12' h3' h6' h10' h9' h15' h7' h13' h1'
    hF hL hI hrg hv r140 re8
  -- reads at the anchor
  have rd0 : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Outside a k (cw sp) → (a + k ≤ zp ∨ zp + 8 * n ≤ a) →
      S'.mem.readLE a k = M.readLE a k := fun a k hh h1 h2 =>
    FvModexp.Expmc.held_readLE hh hF hL h1 (by simp only [outside_cons, outside_nil, and_true]; exact h2)
  have rs : ∀ K, 0x18 ≤ K → K + 8 ≤ 0x3c0 → (K + 8 ≤ 0xe8 ∨ 0xf0 ≤ K) → (K + 8 ≤ 0x118 ∨ 0x128 ≤ K) →
      (K + 8 ≤ 0x138 ∨ 0x148 ≤ K) → (K + 8 ≤ 0x370 ∨ 0x378 ≤ K) → S'.mem.readLE (sp + K) 8 = M.readLE (sp + K) 8 :=
    fun K k1 k2 k3 k4 k5 k6 => rd0 _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))
      (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)
  have hF' : MemFrame M S'.mem (R.rt ++ (cw sp ++ [(zp, zp + 8 * n)])) := by rw [← List.append_assoc]; exact hF
  have hzg := hz.2.2.2.2.2.2.1
  have hzf := hz.2.2.2.2.2.2.2
  unfold Apart at hzg hzf
  have hgo : Outside (g + 16) 8 (cw sp ++ [(zp, zp + 8 * n)]) := by
    unfold Apart at hgw
    simp only [cw, outside_append, outside_cons, outside_nil, and_true]; omega
  have hfo : Outside (fs - 8) 8 (cw sp ++ [(zp, zp + 8 * n)]) := by
    unfold Apart at hfw
    simp only [cw, outside_append, outside_cons, outside_nil, and_true]; omega
  have he' : Env R L g fs sp S'.mem := Env.frame he hF' hgo hfo (LiveExt.refl R L)
  have rdo : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x3c0) →
      Apart zp (8 * zc) a k → S'.mem.readLE a k = M.readLE a k := by
    intro a k hh h1 h2
    unfold Apart at h1 h2
    refine rd0 a k hh (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)
  have hmr : S'.mem.readLE mp (8 * n) = M.readLE mp (8 * n) := rdo _ _ hm.2.2.1 hm.2.2.2 hzm
  have hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp (fun _ => 2 * n) S'.mem := by
    refine ⟨he', hn, hn16, hmc, hmc', hk0, hyl, hyl', inp_frame hm hF, inp_frame hy hF,
      by rw [rdo _ _ hy.2.2.1 hy.2.2.2 hzy]; exact hY, fun d hd => ?_,
      by rw [rs 0x3a8] <;> omega, by rw [rs 0x3b0] <;> omega, by rw [rs 0x3b8] <;> omega, by rw [rs 0xd8] <;> omega,
      by rw [rs 0x398] <;> omega, by rw [rs 0x390] <;> omega, hokS⟩
    obtain ⟨eE1, eE2, eE3, eE4⟩ := hent d hd
    have hbd := hbuf d hd
    refine ⟨inp_frame hbd hF, by rw [rdo _ _ hbd.2.2.1 hbd.2.2.2 (hzt d hd).1]; exact eE1, by show 2 * n < 2 ^ 64; omega,
      ?_, ?_, ?_⟩
    · rw [show sp + 0x1a8 + 24 * d = sp + (0x1a8 + 24 * d) by omega, rs (0x1a8 + 24 * d) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), ← Nat.add_assoc]; exact eE2
    · rw [show sp + 0x1b0 + 24 * d = sp + (0x1b0 + 24 * d) by omega, rs (0x1b0 + 24 * d) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), ← Nat.add_assoc]; exact eE3
    · rw [show sp + 0x1b8 + 24 * d = sp + (0x1b8 + 24 * d) by omega, rs (0x1b8 + 24 * d) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega), ← Nat.add_assoc]; exact eE4
  have hB' : Bufs R L g fs sp n mp yp ylen pp [(onep, 8 * n), (st, 24)] S'.mem zp zc zzp zzc :=
    ⟨buf_frame hz hF, buf_frame hzz hF, hzzz, hzm, hzzm, hzy, hzzy, hzt, hzext⟩
  have hM' : Mem R b L g sp S'.mem S'.mem zp zc zzp zzc :=
    ⟨⟨MemFrame.refl _ _, LiveFrame.refl _ _ _⟩, hI, rfl⟩
  have hws : ∀ q ∈ cw sp ++ [(zp, zp + 8 * n)], q.1 < q.2 → M.accessible q.1 (q.2 - q.1) true = true := by
    intro q hq _
    simp only [cw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals first
      | exact M.accessible_sub hwacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
      | exact M.accessible_sub hz.2.2.1 (Or.inr rfl) (by simp only; omega) (by simp only; omega)
  have hd' : Extracted.program.DataLoaded S'.mem := FvModexp.dataLoaded_frame64 hd hrg hro hF' hws
  have hnm' : NatNorm S'.mem mp n := by
    rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2
      have hz6' := hzm
      unfold Apart at hm4 hz6'
      rw [rd0 _ _ ?_ (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]
      · exact h
      · rcases hm.2.2.1 with h1 | h1
        · exact Or.inl (h1.sub (by omega) (by omega))
        · exact Or.inr (h1.of_sub (by omega) (by omega))
  have hone' : OneIn R L sp n S'.mem onep := by
    rcases hone with h | h
    · exact Or.inl (inp_frame h hF)
    · exact Or.inr h
  have hone1' : S'.mem.readLE onep (8 * n) = 1 := by
    rcases hone with h | ⟨rfl, h4⟩
    · rw [rdo _ _ h.2.2.1 h.2.2.2 (hzext _ (List.mem_cons_self ..)).1]; exact hone1
    · rw [rd0 _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]; exact hone1
  have hfe' : FinEnv sp st n0 bp r S'.mem := by
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
    have hstz := (hzext (st, 24) (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
    have hstw := f12
    unfold Apart at hstz hstw
    refine ⟨f1, f2, f3, by rw [hF.accessible]; exact f4, by rw [rs 0x378] <;> omega, by rw [rs 0x340] <;> omega,
      by rw [rs 0x348] <;> omega, by rw [rs 0x350] <;> omega, f9, by rw [hF.accessible]; exact f10, ?_, f12,
      by rw [rs 0x380] <;> omega, by rw [rs 0x388] <;> omega, f15⟩
    rw [rd0 _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]; exact f11
  have r328' : S'.mem.readLE (sp + 0x328) 8 = onep := by rw [rs 0x328] <;> omega
  have hkk' : (k0 * S'.mem.readLE mp (8 * n) + 1) % Exp.B = 0 := by rw [hmr]; exact hkk
  have hmB' : S'.mem.readLE mp (8 * n) < Exp.B ^ n := by rw [hmr]; exact hmB
  have hyi64 : yi < 2 ^ 64 := by rw [← hyi]; exact Util.readLE8_lt _ _
  have hkt := (kTop_le yi hyi0 hyi64).1
  refine W4Loop.loop hap hclr hmv (ext := [(onep, 8 * n), (st, 24)]) hst r5
    (zjVal n (M.readLE mp (8 * n)) k0 tbl Y ylen yi)
    (fun a b c d => ((a = zp ∧ b = zc ∧ c = zzp ∧ d = zzc) ∨ (a = zzp ∧ b = zzc ∧ c = zp ∧ d = zc)) ∧
      a % 8 = 0 ∧ c % 8 = 0)
    (fun a b c d h => by
      obtain ⟨h1 | h1, h2, h3⟩ := h
      · exact ⟨Or.inr ⟨h1.2.2.1, h1.2.2.2, h1.1, h1.2.1⟩, h3, h2⟩
      · exact ⟨Or.inl ⟨h1.2.2.1, h1.2.2.2, h1.1, h1.2.1⟩, h3, h2⟩)
    ?hexit _ S' (ylen - 1) (kTop yi) ((yi * 2 ^ (64 - kTop yi * 4)) % 2 ^ 64) zp zc zzp zzc rfl (by omega) (by omega)
    (Nat.mod_lt _ (by omega)) (by rw [hpc']; simp only [W4Loop.test, W4Loop.fnE_eq]) hsp' h5' h14' hfs' hx15' hdf'
    h0' h2' h8' h11' h12' h3' h6' h10' h9' h15' h7' h13' h1' hB' hM' r140 re8 (by rw [hmr, hv]) ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, hz8, hzz8⟩
  case hexit =>
    intro Sx zp' zc' zzp' zzc' hpcx hspx h5x h14x hfsx hx15x hdfx h0x h2x h8x h11x h12x h3x h6x h10x hBx hMx r140x
      hvx hPx
    exact ReachesRet.mono (W4Loop.exitRet hap hclr hmv hmk hmvok hwt hro hd' hst hnm' hone' hone1' r328' hkk' hmB' hfe' hsth hbp
      (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) Sx r5 zp' zc' zzp' zzc' hpcx hspx h5x h14x
      hfsx hx15x hdfx h0x h2x h8x h11x h12x h3x h6x h10x hBx hMx r140x hPx.2.2)
      (fun s h => ⟨S'.mem, zp', zc', zzp', zzc', Sx.mem, hPx.1, hF, hL, hrg, hBx, hMx, hvx, h⟩)

end FvModexp.Amd64.W4Pro
