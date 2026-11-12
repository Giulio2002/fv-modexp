import FvModexp.Proofs.Arm64.Exp.SlowAl

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64; text copy of `P2W2Mv`): `runtime.memmove(dst, src, n)` from `SP = sp` (continuation form)
(ported from agent infra's EvMv by agent expmc, scripts/gen/port-ev-slow.py)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- `runtime.memmove`'s contract address -/
abbrev mvE : Nat := 609408

theorem mvE_eq : cA "runtime.memmove" = mvE := by decide

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- **`memmove(dst, src, n)` from `SP = sp`**: the continuation gets the return state, the frame (the runtime, the
window below the saved FP, `dst`), the live frame, the invariant and the copy -/
theorem mvCallW {impl : List Segment} (hmv : MemmoveLive (LibW.program.link impl) mvE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {dst src n ra : Nat} (hra4 : ra % 4 = 0) (hra : ra < 2 ^ 48) (hn : n ≤ 2 ^ 20)
    (hd48 : dst + n ≤ 2 ^ 48) (hdacc : M.accessible dst n true = true) (hdh : Held R L1 dst n)
    (hdw : Apart dst n (sp - K) (K + 544))
    (hs48 : src + n ≤ 2 ^ 48) (hsacc : M.accessible src n false = true) (hsw : Apart src n (sp - K) (K + 544))
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mvE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M) (h0 : T.regs 0 = BitVec.ofNat 64 dst)
    (h1 : T.regs 1 = BitVec.ofNat 64 src) (h2 : T.regs 2 = BitVec.ofNat 64 n) (h30 : T.regs 30 = BitVec.ofNat 64 ra)
    (KC : ∀ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
      (ep : Nat → Bool), MemFrame M m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(dst, dst + n)]) →
      LiveFrame M m L1 [(dst, dst + n)] → R.inv b1 L1 g (view R.rt L1 m) → Mem.Copied M m dst src n →
      m.regions = M.regions → ReachesRet (LibW.program.link impl) ret0 (retStateX T junk [] f v m ex ep) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have e30 : (T.regs 30).toNat = ra := by rw [h30, BitVec.toNat_ofNat]; omega
  have esp : T.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t0 : (T.regs 0).toNat = dst := by rw [h0, BitVec.toNat_ofNat]; omega
  have t1 : (T.regs 1).toNat = src := by rw [h1, BitVec.toNat_ofNat]; omega
  have t2 : (T.regs 2).toNat = n := by rw [h2, BitVec.toNat_ofNat]; omega
  have hok : R.ok mvE [(T.regs 0).toNat, (T.regs 1).toNat, (T.regs 2).toNat] := by
    rw [t0, t1, t2]; exact hsv.2.1 dst src n hn
  obtain ⟨hco, ⟨hgd, hgo⟩, -, hinv, -, hLs, hrt⟩ := wcall hP h T hsp h28 hm (by rw [e30]; exact hra4)
    (by rw [e30]; exact hra) 3 (by omega) mvE _ hok 0 (Nat.zero_le _)
  have hcs : ∀ q ∈ calleeStack T 4096 3, sp - K ≤ q.1 ∧ q.2 ≤ sp + 424 := by
    intro q hq; simp only [calleeStack, esp, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  unfold Apart at hdw hsw
  refine ReachesRet.call_regions (hmv L1 b1) hpc ⟨⟨(guardOK_iff T 4096).1 hgd, hco, hgo⟩, ⟨hok, hinv, hLs, hrt⟩,
    ⟨by rw [t1, t2]; exact hs48, by rw [t1, t2, hm]; exact hsacc, ?_⟩,
    ⟨by rw [t0, t2]; exact hd48, by rw [t0, t2, hm]; exact hdacc, ?_, by rw [t0, t2]; exact hdh⟩⟩ ?_
  · rw [t1, t2]; refine outside_of_forall fun q hq => ?_; have := hcs q hq; omega
  · rw [t0, t2]; refine outside_of_forall fun q hq => ?_; have := hcs q hq; omega
  intro S2 _ ⟨junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hinv2, hcp⟩ hrg0
  subst hs2
  have hg24 := hP.1.2.2.1
  have eg : (T.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  simp only [t0, t1, t2, hm] at hfr2 hlf2 hcp
  rw [eg] at hinv2
  simp only [calleeStack, esp] at hfr2
  exact KC junk f2 v2 m' ex2 ep2 hfr2 hlf2 hinv2 hcp (by rw [← hm]; exact hrg0)

/-- an entry-relative scratch nat is apart from the window -/
theorem scr_win (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {L1 : List (Nat × Nat)} {M : Memory} {t k : Nat}
    (hs : Scr R L L1 s.mem M st t k) : Apart t (8 * k) (sp - K) (K + 544) := by
  rcases hs.loc with ⟨hc0, l1, l2⟩ | ⟨hin, -⟩
  · have := (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc0).1
    unfold Apart at this ⊢; omega
  · exact (hin.apart hP.win_rt).symm

/-- reads of a held range apart from the window and from `dst` are kept by a `memmove` -/
theorem mv_rdH {M M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(d, d + n)]))
    (hLF : LiveFrame M M' L1 [(d, d + n)]) (hK : 4096 ≤ K) {a k : Nat} (hh : Held R L1 a k)
    (hw : Apart a k (sp - K) (K + 544)) (hd : Apart a k d n) : M'.readLE a k = M.readLE a k := by
  unfold Apart at hw hd
  rcases hh with hL | hO
  · exact hLF.readLE a k hL (by simp only [outside_cons, outside_nil, and_true]; omega)
  · exact hF.readLE a k (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨hO, by omega, by omega⟩, by omega⟩)

/-- window reads (outside the callee's stack) apart from `dst` are kept by a `memmove` -/
theorem mv_rdW (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(d, d + n)])) {a k : Nat}
    (ha : sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 32 ≤ a ∧ a + k ≤ sp + 544) (hd : Apart a k d n) :
    M'.readLE a k = M.readLE a k := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  unfold Apart at hd
  exact hF.readLE a k (by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)

set_option maxRecDepth 20000 in
/-- **`WC` through a `memmove` into `[d, d + n)`** (held, apart from the header, inside what the function may write) -/
theorem WC.mv (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(d, d + n)]))
    (hLF : LiveFrame M M' L1 [(d, d + n)]) (hrg : M'.regions = M.regions) (hinv : R.inv b1 L1 g (view R.rt L1 M'))
    (hdhd : Apart d n st 24)
    (hdo : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st s.mem) → Outside a k [(d, d + n)])
    (hdL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(d, d + n)]) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 544) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hhd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF hLF (by omega) (h.sok.2.1.sub (by omega) (by omega))
      (by unfold Apart at hstw ⊢; omega) (by unfold Apart at hdhd ⊢; omega)
  have e0 : stW M' st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen M' st = stLen M st := hhd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hhd 16 (by omega)
  rw [List.append_assoc] at hF
  refine h.call hF hLF hrg (fun a k o1 o2 o3 o4 => ?_) hdL (LiveExt.refl R L1) hinv
    (stkOK_hdr h.sok hF e0 e1 e2 (LiveExt.refl R L1)) (e1.trans h.len) (Nat.le_refl _) (Or.inl ⟨e0, e2⟩)
    (fun hn => absurd ⟨e0, e2⟩ hn)
  have := hdo a k (by rw [outside_append, outside_append]; exact ⟨⟨o1, o2⟩, o4⟩)
  simp only [WN, outside_append, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at o2 this ⊢
  omega


set_option maxRecDepth 20000 in
/-- **`memmove(dst, src, 0)` from `SP = sp`** (`MemmoveZeroLive`, no accessibility asked): only the runtime and the
callee's stack change -/
theorem mvCallZ {impl : List Segment} (hmz : MemmoveZeroLive (LibW.program.link impl) mvE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {ra : Nat} (hra4 : ra % 4 = 0) (hra : ra < 2 ^ 48)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mvE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M) (h2 : T.regs 2 = BitVec.ofNat 64 0)
    (h30 : T.regs 30 = BitVec.ofNat 64 ra)
    (KC : ∀ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
      (ep : Nat → Bool), MemFrame M m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)]) →
      LiveFrame M m L1 [] → R.inv b1 L1 g (view R.rt L1 m) →
      m.regions = M.regions → ReachesRet (LibW.program.link impl) ret0 (retStateX T junk [] f v m ex ep) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have e30 : (T.regs 30).toNat = ra := by rw [h30, BitVec.toNat_ofNat]; omega
  have esp : T.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t2 : (T.regs 2).toNat = 0 := by rw [h2]; rfl
  have hok : R.ok mvE [(T.regs 0).toNat, (T.regs 1).toNat, (T.regs 2).toNat] := by
    rw [t2]; exact hsv.2.1 _ _ 0 (by decide)
  obtain ⟨hco, ⟨hgd, hgo⟩, -, hinv, -, hLs, hrt⟩ := wcall hP h T hsp h28 hm (by rw [e30]; exact hra4)
    (by rw [e30]; exact hra) 3 (by omega) mvE _ hok 0 (Nat.zero_le _)
  refine ReachesRet.call_regions (hmz L1 b1) hpc ⟨t2, ⟨(guardOK_iff T 4096).1 hgd, hco, hgo⟩, hok, hinv, hLs, hrt⟩ ?_
  intro S2 _ ⟨junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hinv2, _⟩ hrg0
  subst hs2
  have hg24 := hP.1.2.2.1
  have eg : (T.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  simp only [hm, List.append_nil] at hfr2 hlf2
  rw [eg] at hinv2
  simp only [calleeStack, esp] at hfr2
  exact KC junk f2 v2 m' ex2 ep2 hfr2 hlf2 hinv2 (by rw [← hm]; exact hrg0)

end

end FvModexp.Arm64.ExpSlow
