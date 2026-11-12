import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Loop
import FvModexp.Proofs.Arm64.Exp.W2P01Defs
import FvModexp.Proofs.Arm64.Exp.W2Tail
import FvModexp.Proofs.Arm64.Exp.W2Zc

/-!
# window-2 (arm64): from the join after `z = z.make(2n)` (`zj`) to the return

`zcopy` (first window) → anchor `M0` = memory at the loop test → `W2Loop.loop` → `W2Tail.exitRet`.
The conclusion packages the anchor and the exit buffers (`ZjPost`); the function theorem composes the frames.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step)

theorem reaches_mono {p : Program} {s : State} {Q Q' : Outcome → Prop} (h : Reaches p s Q) (hq : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h1, h2⟩ := h
  exact ⟨n, o, h1, hq o h2⟩

theorem isReturn_mono {P P' : State → Prop} (hq : ∀ s, P s → P' s) : ∀ o, IsReturn P o → IsReturn P' o := by
  intro o h
  cases o <;> simp only [IsReturn] at h ⊢
  all_goals first | exact hq _ h | exact h

theorem test_eq : W2Loop.test = testL := by
  show segAddr LibW.program W2Loop.fn + 0xa10 = 1804480; rw [fnBase']

/-- the window-2 value from the first window: `outerLoop` over the remaining bits of `y` -/
abbrev zjVal (n Mv k0 : Nat) (tbl : Nat → Nat) (Y ylen yi : Nat) : Nat :=
  Exp.outerLoop 2 (step n Mv k0 tbl) Y 32 (ylen - 1) ((yi * 2 ^ (64 - kTop yi * 2)) % 2 ^ 64) (kTop yi)
    (tbl (yi / 2 ^ (kTop yi * 2)))

/-- what `zj → RET` establishes: the anchor `M0` (frame from `M`), the exit buffers and `TailPost` -/
@[reducible] def ZjPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen bp zp zc zzp zzc : Nat)
    (tbl : Nat → Nat) (V : Nat) (st n0 onep : Nat) (r18 r29 : BitVec 64) (M : Memory) (s' : State) : Prop :=
  ∃ (M0 : Memory) (zp' zc' zzp' zzc' : Nat) (Mx : Memory),
    ((zp' = zp ∧ zc' = zc ∧ zzp' = zzp ∧ zzc' = zzc) ∨ (zp' = zzp ∧ zc' = zzc ∧ zzp' = zp ∧ zzc' = zc)) ∧
    MemFrame M M0 (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) ∧ LiveFrame M M0 L [(zp, zp + 8 * n)] ∧
    M0.regions = M.regions ∧
    Bufs R L g sp n mp yp ylen (fun d => bp + 8 * (d * n)) [(onep, 8 * n), (st, 24)] M0 zp' zc' zzp' zzc' ∧
    Mem R b L g sp M0 Mx zp' zc' zzp' zzc' ∧ Mx.readLE zp' (8 * n) = V ∧
    TailPost R b L g sp n mp k0 st n0 zp' zc' zzp' zzc' r18 r29 M0 Mx s'

theorem buf_frame {R : RtInv} {L : List (Nat × Nat)} {g sp n p c : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Buf R L g sp n M p c) (hf : MemFrame M M' ws) : Buf R L g sp n M' p c := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  exact ⟨a1, a2, by rw [hf.accessible]; exact a3, a4⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-2 from `zj` (after `z.make(2n)`) to the return -/
theorem zjRet (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
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
    (hz : Buf R L g sp n M zp zc) (hzz : Buf R L g sp n M zzp zzc)
    (hent : ∀ d, d < 4 → Ent sp n bp tbl M d) (hbuf : ∀ d, d < 4 → Inp R L sp n M (bp + 8 * (d * n)))
    (hB : Bufs R L g sp n mp yp ylen (fun d => bp + 8 * (d * n)) [(onep, 8 * n), (st, 24)] M zp zc zzp zzc)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r712 : M.readLE (sp + 712) 8 = ylen) (r704 : M.readLE (sp + 704) 8 = yp)
    (r736 : M.readLE (sp + 736) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r728 : M.readLE (sp + 728) 8 = mp)
    (r744 : M.readLE (sp + 744) 8 = mc)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hok : ∀ d, R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm : NatNorm M mp n)
    (hone : OneIn R L sp n M onep) (hone1 : M.readLE onep (8 * n) = 1) (r528 : M.readLE (sp + 528) 8 = onep)
    (hkk : (k0 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 752))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 zj) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h13 : S.regs 13 = BitVec.ofNat 64 n) (h14 : S.regs 14 = BitVec.ofNat 64 zc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (ZjPost R b L g sp n mp mc k0 yp ylen bp zp zc zzp zzc tbl
        (zjVal n (M.readLE mp (8 * n)) k0 tbl Y ylen yi) st n0 onep r18 r29 M)) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmvL := MemmoveLive.of_codeIn hc hmv
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hB0 := hB
  obtain ⟨-, -, hzzz, hzm, hzzm, hzy, hzzy, hzt, hz8, hzz8, hz4, hzz4, hzext⟩ := hB0
  have hz6 := hz.2.2.2.2.2.1
  unfold Apart at hz6
  refine zcopy impl R hmvL ret hret _ b L g sp n mp mc k0 yp ylen bp zp zc zzp zzc tbl M r18 f29 he hn hn16 hz
    hzz.1 hzz.2.1 hy hyl hyl' (by rw [hyi]; exact hyi0) hent hbuf (fun d hd => (hzt d hd).1) r168 r400 r712 r704
    r736 r224 r728 r744 hok hinv S hpc hsp h0 h13 h14 h18 h28 h29 hmem ?_
  intro S' M0 hpc' hsp' h0' h13' h14' h1' h3' h15' h2' h9' h11' h12' h16' h17' h19' h20' h21' h18' h28' h29' hm'
    hF hL hI hrg hv h240
  rw [hyi] at h20' h21' hv
  -- reads at the anchor
  have rd0 : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Outside a k (cw sp) → (a + k ≤ zp ∨ zp + 8 * n ≤ a) →
      M0.readLE a k = M.readLE a k := fun a k hh h1 h2 =>
    FvModexp.Expmc.held_readLE hh hF hL h1 (by simp only [outside_cons, outside_nil, and_true]; exact h2)
  have rs : ∀ K, 32 ≤ K → K + 8 ≤ 752 → (K + 8 ≤ 144 ∨ 152 ≤ K) → (K + 8 ≤ 184 ∨ 192 ≤ K) →
      (K + 8 ≤ 232 ∨ 248 ≤ K) → (K + 8 ≤ 296 ∨ 304 ≤ K) → (K + 8 ≤ 328 ∨ 336 ≤ K) →
      (K + 8 ≤ 368 ∨ 376 ≤ K) → (K + 8 ≤ 584 ∨ 592 ≤ K) → M0.readLE (sp + K) 8 = M.readLE (sp + K) 8 :=
    fun K k1 k2 k3 k4 k5 k6 k7 k8 k9 => rd0 _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))
      (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)
  have hF' : MemFrame M M0 (R.rt ++ (cw sp ++ [(zp, zp + 8 * n)])) := by rw [← List.append_assoc]; exact hF
  have hzc := hz.1
  have hzg := hz.2.2.2.2.2.2
  unfold Apart at hzg
  have hgo : Outside (g + 16) 8 (cw sp ++ [(zp, zp + 8 * n)]) := by
    unfold Apart at hgw
    simp only [cw, outside_append, outside_cons, outside_nil, and_true]; omega
  have he' : Env R L g sp M0 := env_frame he hF' hgo
  -- objects apart from the window and from z[0:n] read at the anchor as at `M`
  have rdo : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4288) (4288 + 752) →
      Apart zp (8 * zc) a k → M0.readLE a k = M.readLE a k := by
    intro a k hh h1 h2
    unfold Apart at h1 h2
    refine rd0 a k hh (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)
  have hmr : M0.readLE mp (8 * n) = M.readLE mp (8 * n) := rdo _ _ hm.2.2.1 hm.2.2.2 hzm
  have hst : Static R L g sp n mp mc k0 yp ylen Y tbl (fun d => bp + 8 * (d * n)) (fun _ => 2 * n) M0 := by
    refine ⟨he', hn, hn16, hmc, hmc', hk0, hyl, hyl', inp_frame hm hF, inp_frame hy hF,
      by rw [rdo _ _ hy.2.2.1 hy.2.2.2 hzy]; exact hY, fun d hd => ?_, by rw [rs 728] <;> omega,
      by rw [rs 736] <;> omega, by rw [rs 744] <;> omega, by rw [rs 224] <;> omega, by rw [rs 712] <;> omega,
      by rw [rs 704] <;> omega, hokS⟩
    obtain ⟨eE1, eE2, eE3, eE4⟩ := hent d hd
    have hbd := hbuf d hd
    refine ⟨inp_frame hbd hF, by rw [rdo _ _ hbd.2.2.1 hbd.2.2.2 (hzt d hd).1]; exact eE1, by show 2 * n < 2 ^ 64; omega,
      ?_, ?_, ?_⟩
    · rw [show sp + 432 + 24 * d = sp + (432 + 24 * d) by omega, rs (432 + 24 * d) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), ← Nat.add_assoc]; exact eE2
    · rw [show sp + 440 + 24 * d = sp + (440 + 24 * d) by omega, rs (440 + 24 * d) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), ← Nat.add_assoc]; exact eE3
    · rw [show sp + 448 + 24 * d = sp + (448 + 24 * d) by omega, rs (448 + 24 * d) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), ← Nat.add_assoc]; exact eE4
  have hB' : Bufs R L g sp n mp yp ylen (fun d => bp + 8 * (d * n)) [(onep, 8 * n), (st, 24)] M0 zp zc zzp zzc :=
    ⟨buf_frame hz hF, buf_frame hzz hF, hzzz, hzm, hzzm, hzy, hzzy, hzt, hz8, hzz8, hz4, hzz4, hzext⟩
  have hM' : Mem R b L g sp M0 M0 zp zc zzp zzc := ⟨MemFrame.refl _ _, ⟨fun _ _ _ _ => rfl⟩, hI, rfl⟩
  -- the exit environment at the anchor
  have hws : ∀ r ∈ cw sp ++ [(zp, zp + 8 * n)], r.1 < r.2 → M.accessible r.1 (r.2 - r.1) true = true := by
    have hacc4 := hce.2.2.2.1
    intro r hr _
    simp only [cw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals first
      | exact M.accessible_sub hacc4 (Or.inr rfl) (by simp only; omega) (by simp only; omega)
      | exact M.accessible_sub hz.2.2.1 (Or.inr rfl) (by simp only; omega) (by simp only; omega)
  have hce' : CallW.CEnv R L g sp 4304 752 M0 := CallW.CEnv.frame hce hF' hrg hws hgo
  have hnm' : NatNorm M0 mp n := by
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
  have hone' : OneIn R L sp n M0 onep := by
    rcases hone with h | h
    · exact Or.inl (inp_frame h hF)
    · exact Or.inr h
  have hone1' : M0.readLE onep (8 * n) = 1 := by
    rcases hone with h | ⟨rfl, h4⟩
    · rw [rdo _ _ h.2.2.1 h.2.2.2 (hzext _ (List.mem_cons_self ..)).1]; exact hone1
    · rw [rd0 _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]; exact hone1
  have hfe' : FinEnv sp g st n0 r29 ret M0 := by
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hfe
    have hgr : M0.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
      hF'.readLE _ _ (by simp only [outside_append] at hgo ⊢; exact ⟨hgrt, hgo⟩)
    have hstz := (hzext (st, 24) (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
    have hstw := hstw4
    unfold Apart at hstz hstw
    refine ⟨f1, f2, f3, by rw [hF.accessible]; exact f4, f5, by rw [hF.accessible]; exact f6, by rw [hgr]; exact f7, f8,
      by rw [rs 624] <;> omega, by rw [rs 552] <;> omega, by rw [rs 560] <;> omega, by rw [rs 568] <;> omega, f13,
      by rw [hF.accessible]; exact f14, ?_, f16, f17, ?_, ?_⟩
    · rw [rd0 _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
        (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]; exact f15
    · rw [rd0 _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]; exact f18
    · rw [rd0 _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (by simp only [cw, outside_cons, outside_nil, and_true]; omega) (by omega)]; exact f19
  have hkk' : (k0 * M0.readLE mp (8 * n) + 1) % Exp.B = 0 := by rw [hmr]; exact hkk
  have hmB' : M0.readLE mp (8 * n) < Exp.B ^ n := by rw [hmr]; exact hmB
  have hmw4' := hmw4
  refine W2Loop.loop impl hap R hclr hmv ret hret _ b L g sp n mp mc k0 yp ylen Y tbl (fun d => bp + 8 * (d * n))
    (fun _ => 2 * n) (ext := [(onep, 8 * n), (st, 24)]) M0 r18 f29 (zjVal n (M.readLE mp (8 * n)) k0 tbl Y ylen yi)
    (fun a b c d => (a = zp ∧ b = zc ∧ c = zzp ∧ d = zzc) ∨ (a = zzp ∧ b = zzc ∧ c = zp ∧ d = zc))
    (fun a b c d h => by rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> simp [h1, h2, h3, h4]) hst
    ?hexit _ S' (ylen - 1) (kTop yi) ((yi * 2 ^ (64 - kTop yi * 2)) % 2 ^ 64) zp zc zzp zzc M0 rfl ?_ (by omega)
    (Nat.mod_lt _ (by omega)) (by rw [test_eq]; exact hpc') hsp' h0' h13' h14' h1' h3' h15' h2' h9' h11' h12' h16'
    h17' h19' h20' h21' h18' h28' h29' hm' hB' hM' h240 ?_ (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  case hexit =>
    intro Sx zp' zc' zzp' zzc' Mx hpcx hspx h0x h1x h13x h14x h15x h2x h3x h9x h11x h12x h18x h28x h29x hmx hBx hMx hvx hPx
    exact reaches_mono (W2Loop.exitRet impl hap R hclr hmv hmk hserv ret hret b L g sp n mp mc k0 yp ylen Y tbl
      (fun d => bp + 8 * (d * n)) (fun _ => 2 * n) M0 r18 r29 f29 onep st n0 hst hce' hmw4' hnm' hone' hone1'
      (by rw [rs 528] <;> omega) hkk' hmB' hfe' hsth hstw4 (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) Sx zp' zc' zzp' zzc' Mx hpcx hspx h0x h1x h13x h14x h15x h2x
      h3x h9x h11x h12x h18x h28x h29x hmx hBx hMx)
      (isReturn_mono (fun s h => ⟨M0, zp', zc', zzp', zzc', Mx, hPx, hF, hL, hrg, hBx, hMx, hvx, h⟩))
  · have := (kTop_le yi hyi0 (by rw [← hyi]; exact Util.readLE8_lt _ _)).1; omega
  · rw [hmr, hv]

end FvModexp.Arm64.W2Pro
