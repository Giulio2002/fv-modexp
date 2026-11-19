import FvModexp.Proofs.Amd64.Exp.P2W4UB
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `runtime.memmove(dst, src, n)` called at `RSP = sp - 0x8` under `WC`
(agent divmc s76, port of divmc s71; amd64 twin of agent infra's `Arm64.P2W4Mv`, call shape of agent asm's amd64 `ExpEven.mvCall`)

* `mvCallW`: `memmove(d, src, n)` with `0 < n` (`RAX = d`, `RBX = src`, `RCX = n`); the callee's window
  `calleeStack64 = [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)]` lies in `WN`.
* `scr_win`, `mv_rdH`, `mv_rdW`, `WC.mv`: reads and `WC` through the copy.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- `runtime.memmove`'s contract address (= `P2Pre.mvE`) -/
abbrev mvE : Nat := 4763104
theorem mvE_eq : Extracted.program.contractAddr "runtime.memmove" = mvE := by decide

/-- an opaque wrapper (keeps big facts out of `janus64_run`'s context splitting; as `P2W2R1b.Hd`) -/
structure HdM (P : Prop) : Prop where
  h : P

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

/-- the stack's array (when nonempty) is apart from the window -/
theorem EPre.arr_win (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) :
    0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 0x8 - K) (K + 0x360) := by
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, harr, -⟩ := hP'
  exact fun h => (harr h).1

/-- an entry-relative scratch nat is apart from the window -/
theorem scr_win (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {t k : Nat}
    (hs : Scr R L L1 s.mem M st t k) : Apart t (8 * k) (sp - 0x8 - K) (K + 0x360) := by
  rcases hs.loc with ⟨hc0, l1, l2⟩ | ⟨hin, -⟩
  · have := hP.arr_win hc0
    unfold Apart at this ⊢; omega
  · exact (hin.apart hP.win_rt).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`memmove(d, src, n)` from `RSP = sp - 0x8`**, `0 < n` (continuation form) -/
theorem mvCallW {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    {d src n : Nat} (hn : n ≤ 2 ^ 20) (hd64 : d < 2 ^ 64) (hs64 : src < 2 ^ 64)
    (hs48 : src + n ≤ 2 ^ 48) (hsacc : M.accessible src n false = true) (hsw : Apart src n (sp - 0x8 - K) (K + 0x360))
    (hd48 : d + n ≤ 2 ^ 48) (hdacc : M.accessible d n true = true) (hdh : Held R L1 d n)
    (hdw : Apart d n (sp - 0x8 - K) (K + 0x360))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mvE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hm : T.mem = M) (hra : M.readLE (sp - 0x8) 8 < 2 ^ 47)
    (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (h0 : T.regs 0 = BitVec.ofNat 64 d) (h3 : T.regs 3 = BitVec.ofNat 64 src) (h1 : T.regs 1 = BitVec.ofNat 64 n)
    (KC : ∀ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256)
      (kr : Nat → W64),
      MemFrame M m (R.rt ++ [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)] ++ [(d, d + n)]) →
      LiveFrame M m L1 [(d, d + n)] → R.inv (b1 + stkR H M st) L1 g (view R.rt L1 m) → Mem.Copied M m d src n →
      m.regions = M.regions → ReachesRet (LibW.program.link impl) ret0 (retState64 T junk [] f x yh m zh kr) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hce := h.cenv hP
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, -, -, -, -, -, -, -, -⟩ := hce
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  have t4 : (T.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t14 : (T.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have t0 : (T.regs 0).toNat = d := by rw [h0, BitVec.toNat_ofNat]; omega
  have t3 : (T.regs 3).toNat = src := by rw [h3, BitVec.toNat_ofNat]; omega
  have t1 : (T.regs 1).toNat = n := by rw [h1, BitVec.toNat_ofNat]; omega
  have hok : R.ok mvE [d, src, n] := by rw [← mvE_eq]; exact hsv.2.1 d src n hn
  have hacc : M.accessible (sp - 0x8 - 4096) (4096 + 8 + 8 * 3) true = true :=
    Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)
  unfold Apart at c9 hsw hdw
  refine ReachesRet.call_regions (hmv L1 (b1 + stkR H M st)) hpc ?_ ?_
  · simp only [MemPre64, MemAmd64.EqPre, MemAmd64.CallOK, LiveMemAt64, liveWin64, MemAmd64.Input, LiveDest64,
      MapAmd64.calleeStack, calleeStack64, t4, t0, t1, t3, t14, hm, hx15, hdf, List.cons_append, List.nil_append,
      outside_cons, outside_nil, and_true]
    refine ⟨⟨?_, ⟨by omega, by omega, by omega, hacc, trivial, trivial, hra⟩, by omega⟩, ⟨hok, h.inv, ?_, ?_⟩,
      ⟨hs48, hsacc, by omega⟩, ⟨hd48, hdacc, by omega, hdh, by omega⟩⟩
    · exact ⟨by simp only [regG, stackguard0Offset, t14]; omega, by simp only [regG, stackguard0Offset, t14, hm]; exact c6,
        by simp only [stackguard0, regG, regSP, stackguard0Offset, t14, hm, t4]; omega, by simp only [regG, regSP, stackguard0Offset, t14, hm, t4]; omega⟩
    · intro q hq
      have := c11 q hq
      simp only [outside_cons, outside_nil, and_true] at this ⊢
      omega
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
  intro S2 _ ⟨junk, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hinv2, hcp⟩ hrg0
  subst hs2
  simp only [t0, t1, t3, hm, calleeStack64, t4, t14] at hfr2 hlf2 hinv2 hcp
  have e8 : sp - 0x8 + 8 = sp := by omega
  rw [e8, show sp + 0x8 * 3 = sp + 0x18 by omega] at hfr2
  exact KC junk f2 x2 yh2 m' zh2 kr2
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfr2)
    hlf2 hinv2 hcp (by rw [← hm]; exact hrg0)

/-- reads of a held range apart from the window and from `d` are kept by a `memmove` -/
theorem mv_rdH {M M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)] ++ [(d, d + n)]))
    (hLF : LiveFrame M M' L1 [(d, d + n)]) (hK : 4096 ≤ K) {a k : Nat} (hh : Held R L1 a k)
    (hw : Apart a k (sp - 0x8 - K) (K + 0x360)) (hd : Apart a k d n) : M'.readLE a k = M.readLE a k := by
  unfold Apart at hw hd
  rcases hh with hL | hO
  · exact hLF.readLE a k hL (by simp only [outside_cons, outside_nil, and_true]; omega)
  · exact hF.readLE a k (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨hO, by omega, by omega⟩, by omega⟩)

/-- window reads outside the callee's stack and apart from `d` are kept by a `memmove` -/
theorem mv_rdW (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)] ++ [(d, d + n)])) {a k : Nat}
    (ha : sp - 0x8 ≤ a ∧ a + k ≤ sp ∨ sp + 0x18 ≤ a ∧ a + k ≤ sp + 0x358) (hd : Apart a k d n) :
    M'.readLE a k = M.readLE a k := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hout := hP.win_rt
  unfold Apart at hd
  exact hF.readLE a k (by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)

set_option maxRecDepth 20000 in
/-- **`WC` through a `memmove` into `[d, d + n)`** (held, apart from the header, inside what the function may write) -/
theorem WC.mv (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)] ++ [(d, d + n)]))
    (hLF : LiveFrame M M' L1 [(d, d + n)]) (hrg : M'.regions = M.regions)
    (hinv : R.inv (b1 + stkR H M st) L1 g (view R.rt L1 M'))
    (hdhd : Apart d n st 24)
    (hdo : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st s.mem) → Outside a k [(d, d + n)])
    (hdL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(d, d + n)]) :
    WC R H L K g sp st zp zc s.mem M' L1 b1 ℓ := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  have hhd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF hLF (by omega) (h.sok.2.1.sub (by omega) (by omega))
      (by unfold Apart at hstw ⊢; omega) (by unfold Apart at hdhd ⊢; omega)
  have e0 : stW M' st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen M' st = stLen M st := hhd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hhd 16 (by omega)
  rw [List.append_assoc] at hF
  refine h.call hF hLF hrg (fun a k o1 o2 o3 o4 => ?_) hdL (LiveExt.refl R L1) (by rw [stkR_congr e2]; exact hinv)
    (stkOK_hdr h.sok hF e0 e1 e2 (LiveExt.refl R L1)) (e1.trans h.len) (Nat.le_refl _) (Or.inl ⟨e0, e2⟩)
    (fun hn => absurd ⟨e0, e2⟩ hn)
  have := hdo a k (by rw [outside_append, outside_append]; exact ⟨⟨o1, o2⟩, o4⟩)
  simp only [WN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at o2 this ⊢
  omega

end

end FvModexp.Amd64.P2W4
