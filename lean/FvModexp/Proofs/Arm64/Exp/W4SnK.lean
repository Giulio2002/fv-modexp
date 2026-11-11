import FvModexp.Proofs.Arm64.Exp.W4Ctx

/-!
# window-4 (arm64): a `stk.nat(k)` call at any call site (`snCallK`), and its `Keeps` (`keeps_sn`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `stk.nat(k)` from the entry of `(*stack).nat` (return address `ra`) to `ra` -/
theorem snCallK (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hSN : StackNat.Hyp impl R StackNat.names 4208 24)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp k st ra : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (hRA : RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) ra) (hra : ra < 2 ^ 64)
    (hpre : SnPre R b L g sp st k M) (hst : st < 2 ^ 64) (hk : 0 < k)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 snE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 k)
    (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KB : ∀ (S' : State) (M' : Memory) (L' : List (Nat × Nat)) (b' : Nat),
      S'.pc = BitVec.ofNat 64 ra → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 (stW M' st + 8 * stLen M st) → S'.regs 1 = BitVec.ofNat 64 k →
      S'.regs 2 = BitVec.ofNat 64 k →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      SnPost R b L L' b' g sp st k M M' →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨hce, hserv, hsok, hstw, harr, hk16, hlen, hcost, hinv, hwba, hstwb, hstf⟩ := hpre
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hns : ∀ x, StackNat.names.contains x = true → LibExp.names.contains x = true := MontW.sub_of_all (by decide)
  have hS0 := CallW.hypSum hap hns (hSN b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 k))
  rw [show segAddr Extracted.program StackNat.fn = snE by decide] at hS0
  have tst := toNat_lt' hst
  have tk : (BitVec.ofNat 64 k).toNat = k := toNat_lt' (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt' (by omega)
  have tg : (S.regs 28).toNat = g := by rw [h28]; exact toNat_lt' (by omega)
  refine Reaches.call_regions (hS0.withExit hret) hpc ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [h30, toNat_lt' hra]; exact hRA
  case args =>
    simp only [ArgsFrom]
    exact ⟨h0, h1, trivial⟩
  case pre =>
    simp only [StackNat.Pre]
    rw [tst, tk, hmem]
    have hce' := CallW.callEnv_of hce hsp h28 hmem (stk := 4208) (above := 24) (by omega) (by omega)
    simp only [win, tsp, tg]
    unfold Apart at hstw
    refine ⟨hce', hserv, hsok, by simp only [outside_cons, outside_nil, and_true]; omega, fun hc => ?_, hk16, hlen,
      hcost, hinv, hwba, hstwb, hstf⟩
    obtain ⟨a1, a2⟩ := harr hc
    unfold Apart at a1
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, a2⟩
  obtain ⟨hX0, hX1, hX2, L', b', ⟨hLE, hb', hinv'⟩, hsok', hlen', hkept, hfresh, hF, hLF⟩ := hq
  simp only [tst, tk, hmem, tsp, tg, winA] at hX0 hX1 hX2 hb' hinv' hsok' hlen' hkept hfresh hF hLF
  refine KB s' s'.mem L' b' (hr.trans h30) (e1.trans hsp) (hX0 hk) hX1 hX2 (e4.trans h18) (e2.trans h28) (e3.trans h29)
    rfl ⟨hLE, hb', hinv', hsok', hlen', hkept, hfresh, hF, hLF, by rw [hrg, hmem]⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a `stk.nat(k)` call keeps the context -/
theorem keeps_sn {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret b b' k : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)} {M M' : Memory}
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) (hk : 0 < k)
    (hS : SnPost R b L L' b' g sp st k M M') : Keeps R L L' g sp K st l0 ex M M' := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960, r904, r328, r320⟩ := hC
  obtain ⟨hxS, hbS, hinvS, hsok2, hlen2, hkept, hfresh, hFS, hLS, hrgS⟩ := hS
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro'⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  have hr : 0 < StackNat.rnd k := by simp only [StackNat.rnd]; omega
  have hstg := hfe.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [AW, Apart, stUp] at hstw huw hug hsu hga hstg
  refine keeps_of hce hK hxS (by simpa only [List.append_assoc] using hFS) hLS hrgS ?_ ?_ ?_ ?_ ?_ ?_ hsok2
    (by omega) ?_ ?_
  · intro r hr' hlt
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · intro a k' ho
    obtain ⟨-, o2, o3, o4, -⟩ := ho
    simp only [AW, Apart, stUp] at o2 o3 o4
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  · intro j hj
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
    · exact Or.inl (hkept hc)
    · exact Or.inr (hfresh (by omega))
  · intro _
    by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
    · rw [(hkept hc).2]; exact hcap
    · have := hsok2.2.2.2.2.2.1; simp only [stLen, stCap] at hlen2 this ⊢; omega

end FvModexp.Arm64.W4Pro
