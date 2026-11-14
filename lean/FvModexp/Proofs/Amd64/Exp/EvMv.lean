import FvModexp.Proofs.Amd64.Exp.EvJ
import FvModexp.Proofs.Amd64.Nat.StackNatCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `runtime.makeslice` / `runtime.memmove` called at `RSP = sp - 8` under `WC` (asm s60; twin of
infra's arm64 `EvAl` / `EvMv`)

* `WC.alloc`, `AllocR`, `mkCall`: `makeslice(Word, n, c)` (`RAX = type:big.Word`, `RBX = n`, `RCX = c`); the callee's
  window `calleeStack64 = [(sp - 8 - 4096, sp - 8), (sp, sp + 24)]` lies in `WN`.
* `mvCall`: `memmove(d, src, n)` (`MemmoveLive64.withZero`: an empty copy asks nothing of `d`, `src`), `WC.mv`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `runtime.makeslice` / `runtime.memmove` contract addresses -/
abbrev mkE : Nat := 4739904
abbrev mvE : Nat := 4763104

theorem mkE_eq : cA "runtime.makeslice" = mkE := by decide
theorem mvE_eq : cA "runtime.memmove" = mvE := by decide
theorem wT_eq : StackNat.wT = 7233184 := by decide

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a range of the window below the saved `RBP` is outside `WN`'s complement -/
theorem cs_out {a k : Nat} {cs : List (Nat × Nat)} (hcs : ∀ q ∈ cs, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x148)
    (ho : Outside a k (WN sp K)) : Outside a k cs := by
  simp only [WN, outside_cons, outside_nil, and_true] at ho
  refine outside_of_forall fun q hq => ?_
  have := hcs q hq; omega

/-- the stack header through a step that writes only the runtime's ranges and `cs` (in the window), keeping `L1` -/
theorem hdr_keep (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x148) (hLF : LiveFrame M m L1 []) {a k : Nat} (h1 : st ≤ a)
    (h2 : a + k ≤ st + 24) : m.readLE a k = M.readLE a k := by
  have hstw := hP.stkF.1
  unfold Apart at hstw
  rcases h.sok.2.1 with hL | hO
  · exact hLF.readLE a k (hL.sub h1 h2) trivial
  · refine hMF.readLE a k ?_
    rw [outside_append]
    refine ⟨hO.of_sub h1 h2, outside_of_forall fun q hq => ?_⟩
    have := hcs q hq; omega

/-- **`WC` through a live allocation** of `[p, p + r)` -/
theorem WC.alloc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x148) (hLF : LiveFrame M m L1 []) (hrg : m.regions = M.regions)
    {p n : Nat} (hin : InRanges p n R.rt) (hap : ApartAll p n L1)
    (hinv : R.inv (b1 - n) (L1 ++ [(p, p + n)]) g (view R.rt (L1 ++ [(p, p + n)]) m)) :
    WC R L K g sp st zp zc s.mem m (L1 ++ [(p, p + n)]) (b1 - n) ℓ := by
  have e0 : stW m st = stW M st := hdr_keep hP h hMF hcs hLF (Nat.le_refl _) (by omega)
  have e1 : stLen m st = stLen M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have e2 : stCap m st = stCap M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + n)]) :=
    LiveExt.single (by rw [show p + n - p = n by omega]; exact hin) (by rw [show p + n - p = n by omega]; exact hap)
  refine h.call hMF hLF hrg (fun a k _ o2 _ _ => cs_out hcs o2) (fun _ _ _ _ => trivial) hx hinv
    (stkOK_hdr h.sok hMF e0 e1 e2 hx) (e1.trans h.len) (Nat.le_refl _) (Or.inl ⟨e0, e2⟩)
    (fun hn => absurd ⟨e0, e2⟩ hn)

theorem alloc_rd (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {m : Memory}
    {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x148) (hLF : LiveFrame M m L1 []) {a k : Nat}
    (hh : Held R L1 a k) (hap : Apart a k (sp - 8 - K) (K + 0x1c0)) : m.readLE a k = M.readLE a k := by
  rcases hh with hL | hO
  · exact hLF.readLE a k hL trivial
  · refine hMF.readLE a k ?_
    rw [outside_append]
    unfold Apart at hap
    refine ⟨hO, outside_of_forall fun q hq => ?_⟩
    have := hcs q hq; omega

end

/-- the facts after a live allocation of `[p, p + rr)` (`n` bytes asked) at a call from `RSP = sp - 8`, memory `M → m` -/
structure AllocR (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory) (L1 : List (Nat × Nat))
    (b1 ℓ : Nat) (m : Memory) (p rr n : Nat) : Prop where
  wc : WC R L K g sp st zp zc m0 m (L1 ++ [(p, p + rr)]) (b1 - rr) ℓ
  rin : InRanges p rr R.rt
  rap : ApartAll p rr L1
  b48 : p + rr ≤ 2 ^ 48
  acc : m.accessible p rr true = true
  al : p % 8 = 0
  sz : n ≤ rr
  rc : rr ≤ allocCost n
  keep : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp ∨ sp + 24 ≤ a ∧ a + k ≤ sp + 0x1b8) → m.readLE a k = M.readLE a k
  rdH : ∀ a k, Held R L1 a k → Apart a k (sp - 8 - K) (K + 0x1c0) → m.readLE a k = M.readLE a k
  macc : ∀ a k w, m.accessible a k w = M.accessible a k w

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`makeslice(Word, n, c)` from `RSP = sp - 8`** (continuation form) -/
theorem mkCall {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibNE.program.link impl) mkE 4096 R)
    {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {n c : Nat} (hnc : n ≤ c) (hc0 : 0 < c) (hc : c ≤ 2 ^ 17) (hcost : blockSize (8 * c) true ≤ b1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mkE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hm : T.mem = M) (hra : M.readLE (sp - 8) 8 < 2 ^ 47)
    (h0 : T.regs 0 = BitVec.ofNat 64 7233184) (h3 : T.regs 3 = BitVec.ofNat 64 n) (h1 : T.regs 1 = BitVec.ofNat 64 c)
    (KC : ∀ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64),
      AllocR R L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize (8 * c) true) (8 * c) →
      ReachesRet (LibNE.program.link impl) ret0 (retState64 T junk [ptr] f x yh m zh kr) Q) :
    ReachesRet (LibNE.program.link impl) ret0 T Q := by
  have hk := hP.kf
  have hce := h.cenv hP
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -, -, -, -, -, -, -⟩ := hce
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts c12
  rw [wT_eq] at ht1 ht2 ht3
  have t4 : (T.regs 4).toNat = sp - 8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t14 : (T.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have t0 : (T.regs 0).toNat = 7233184 := by rw [h0]; rfl
  have t3 : (T.regs 3).toNat = n := by rw [h3, BitVec.toNat_ofNat]; omega
  have t1 : (T.regs 1).toNat = c := by rw [h1, BitVec.toNat_ofNat]; omega
  have hsz : typSize T.mem (T.regs 0).toNat * (T.regs 1).toNat = 8 * c := by
    simp only [typSize, t0, t1, hm, ht1]
  have hround : makesliceRound64 T = blockSize (8 * c) true := by
    simp only [makesliceRound64, typSize, typNoscan, typPtrBytes, t0, t1, hm, ht1, ht2]; rfl
  have hacc : M.accessible (sp - 8 - 4096) (4096 + 8 + 8 * 3) true = true :=
    Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)
  have hwT : Apart 7233184 16 (sp - 8 - 4096) (4096 + 8 + 8 * 3) :=
    apart_of_data c12 1 (by decide) (by decide) hacc
  have hok : R.ok mkE [7233184, n, c] := by rw [← mkE_eq]; exact hsv.1 _ _ _ hc
  unfold Apart at hwT c9
  refine ReachesRet.call_regions (hmk.pos L1 b1) hpc ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
  · rw [t4, hm]; exact hra
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4, hm]; exact hacc
  · rw [t0, hm]; exact ⟨by decide, ht3⟩
  · rw [t3, t1]; exact hnc
  · rw [t1]; omega
  · rw [hsz]; simp only [maxAlloc]; omega
  · simp only [calleeStack64, t0, t4, outside_cons, outside_nil, and_true]; omega
  · simp only [GuardOK64, t14, t4, hm]; exact ⟨c5, c6, by omega⟩
  · simp only [calleeStack64, t14, t4, outside_cons, outside_nil, and_true]; omega
  · rw [t0, t3, t1]; exact hok
  · rw [t14, hm]; exact h.inv
  · rw [hround]; exact hcost
  · intro q hq
    have := c11 q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
  · rw [hsz]; omega
  intro S1 _ hpost hrg1
  obtain ⟨ptr, junk, f, x, yh, m, zh, kr, rfl, hMF, hLF, ⟨hobj, hap⟩, -, hinv⟩ := hpost
  simp only [makesliceObj64, Fresh, hsz] at hobj
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, hm, ht2]; rfl
  rw [hround] at hap hinv
  rw [hns] at hobj
  obtain ⟨hin, h48, hacc', hal, -, -, hle⟩ := hobj
  have hcs : ∀ q ∈ calleeStack64 T 4096 3, sp - 8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x148 := by
    intro q hq; simp only [calleeStack64, t4, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  rw [hm] at hMF hLF
  rw [t14] at hinv
  have hrg : m.regions = M.regions := by rw [← hm]; exact hrg1
  have hout := hP.win_rt
  refine KC ptr junk f x yh m zh kr ⟨h.alloc hP hMF hcs hLF hrg hin hap hinv, hin, hap, h48, hacc',
    hal (Or.inr (by omega)), hle, blockSize_le_allocCost _ _, fun a k ha => hMF.readLE a k ?_,
    fun a k hh hap => alloc_rd hP hMF hcs hLF hh hap, hMF.accessible⟩
  rw [outside_append]
  refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
  simp only [calleeStack64, t4, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`memmove(d, src, n)` from `RSP = sp - 8`** (continuation form; `n = 0` asks nothing of `d`, `src`, and then the
written range is reported as the empty `[0, 0)`) -/
theorem mvCall {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibNE.program.link impl) mvE 4096 R) {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {d src n : Nat} (hn : n ≤ 2 ^ 20) (hd64 : d < 2 ^ 64) (hs64 : src < 2 ^ 64)
    (hD : n = 0 ∨ (src + n ≤ 2 ^ 48 ∧ M.accessible src n false = true ∧ Apart src n (sp - 8 - K) (K + 0x1c0) ∧
      d + n ≤ 2 ^ 48 ∧ M.accessible d n true = true ∧ Held R L1 d n ∧ Apart d n (sp - 8 - K) (K + 0x1c0)))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mvE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hm : T.mem = M) (hra : M.readLE (sp - 8) 8 < 2 ^ 47)
    (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (h0 : T.regs 0 = BitVec.ofNat 64 d) (h3 : T.regs 3 = BitVec.ofNat 64 src) (h1 : T.regs 1 = BitVec.ofNat 64 n)
    (KC : ∀ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256)
      (kr : Nat → W64) (dd : Nat), (n = 0 ∧ dd = 0 ∨ dd = d) →
      MemFrame M m (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp, sp + 24)] ++ [(dd, dd + n)]) →
      LiveFrame M m L1 [(dd, dd + n)] → R.inv b1 L1 g (view R.rt L1 m) → Mem.Copied M m d src n →
      m.regions = M.regions → ReachesRet (LibNE.program.link impl) ret0 (retState64 T junk [] f x yh m zh kr) Q) :
    ReachesRet (LibNE.program.link impl) ret0 T Q := by
  have hk := hP.kf
  have hce := h.cenv hP
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, -, -, -, -, -, -, -, -⟩ := hce
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  have t4 : (T.regs 4).toNat = sp - 8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t14 : (T.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have t0 : (T.regs 0).toNat = d := by rw [h0, BitVec.toNat_ofNat]; omega
  have t3 : (T.regs 3).toNat = src := by rw [h3, BitVec.toNat_ofNat]; omega
  have t1 : (T.regs 1).toNat = n := by rw [h1, BitVec.toNat_ofNat]; omega
  have hok : R.ok mvE [d, src, n] := by rw [← mvE_eq]; exact hsv.2.1 d src n hn
  have hacc : M.accessible (sp - 8 - 4096) (4096 + 8 + 8 * 3) true = true :=
    Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)
  unfold Apart at c9
  by_cases hn0 : n = 0
  · subst hn0
    refine ReachesRet.call_regions (hmz L1 b1) hpc ?_ ?_
    · simp only [MemPre64, MemAmd64.EqPre, MemAmd64.CallOK, LiveMemAt64, liveWin64,
        MapAmd64.calleeStack, calleeStack64, t4, t0, t1, t3, t14, hm, hx15, hdf, List.cons_append, List.nil_append,
        outside_cons, outside_nil, and_true]
      refine ⟨trivial, ⟨?_, ⟨by omega, by omega, by omega, hacc, trivial, trivial, hra⟩, by omega⟩, ⟨hok, h.inv, ?_, ?_⟩⟩
      · exact ⟨by simp only [regG, stackguard0Offset, t14]; omega, by simp only [regG, stackguard0Offset, t14, hm]; exact c6,
          by simp only [stackguard0, regG, regSP, stackguard0Offset, t14, hm, t4]; omega⟩
      · intro q hq
        have := c11 q hq
        simp only [outside_cons, outside_nil, and_true] at this ⊢
        omega
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
    intro S2 _ ⟨junk, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hinv2, _⟩ hrg0
    subst hs2
    simp only [hm, calleeStack64, t4, t14, List.append_nil] at hfr2 hlf2 hinv2
    have e8 : sp - 8 + 8 = sp := by omega
    rw [e8, show sp + 8 * 3 = sp + 24 by omega] at hfr2
    exact KC junk f2 x2 yh2 m' zh2 kr2 0 (Or.inl ⟨rfl, rfl⟩)
      (hfr2.mono fun a k ho => by rw [outside_append] at ho; exact ho.1)
      ⟨fun a k hin _ => hlf2.readLE a k hin trivial⟩ hinv2 (fun i hi => absurd hi (by omega)) (by rw [← hm]; exact hrg0)
  refine ReachesRet.call_regions (hmv.withZero hmz L1 b1) hpc ?_ ?_
  · simp only [MemPre64, MemAmd64.EqPre, MemAmd64.CallOK, LiveMemAt64, liveWin64, MemAmd64.Input, LiveDest64,
      MapAmd64.calleeStack, calleeStack64, t4, t0, t1, t3, t14, hm, hx15, hdf, List.cons_append, List.nil_append,
      outside_cons, outside_nil, and_true]
    refine ⟨⟨?_, ⟨by omega, by omega, by omega, hacc, trivial, trivial, hra⟩, by omega⟩, ⟨hok, h.inv, ?_, ?_⟩, ?_⟩
    · exact ⟨by simp only [regG, stackguard0Offset, t14]; omega, by simp only [regG, stackguard0Offset, t14, hm]; exact c6,
        by simp only [stackguard0, regG, regSP, stackguard0Offset, t14, hm, t4]; omega⟩
    · intro q hq
      have := c11 q hq
      simp only [outside_cons, outside_nil, and_true] at this ⊢
      omega
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
    · rcases hD with e | ⟨a1, a2, a3, a4, a5, a6, a7⟩
      · exact Or.inl e
      · unfold Apart at a3 a7
        right
        and_intros <;> first | assumption | omega
  intro S2 _ ⟨junk, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hinv2, hcp⟩ hrg0
  subst hs2
  simp only [t0, t1, t3, hm, calleeStack64, t4, t14] at hfr2 hlf2 hinv2 hcp
  have e8 : sp - 8 + 8 = sp := by omega
  rw [e8, show sp + 8 * 3 = sp + 24 by omega] at hfr2
  exact KC junk f2 x2 yh2 m' zh2 kr2 d (Or.inr rfl) (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hfr2)
    hlf2 hinv2 hcp (by rw [← hm]; exact hrg0)

/-- reads of a held range apart from the window and from `d` are kept by a `memmove` -/
theorem mv_rdH {M M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp, sp + 24)] ++ [(d, d + n)]))
    (hLF : LiveFrame M M' L1 [(d, d + n)]) (hK : 4096 ≤ K) {a k : Nat} (hh : Held R L1 a k)
    (hw : Apart a k (sp - 8 - K) (K + 0x1c0)) (hd : Apart a k d n) : M'.readLE a k = M.readLE a k := by
  unfold Apart at hw hd
  rcases hh with hL | hO
  · exact hLF.readLE a k hL (by simp only [outside_cons, outside_nil, and_true]; omega)
  · exact hF.readLE a k (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨hO, by omega, by omega⟩, by omega⟩)

/-- window reads outside the callee's stack and apart from `d` are kept by a `memmove` -/
theorem mv_rdW (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp, sp + 24)] ++ [(d, d + n)])) {a k : Nat}
    (ha : sp - 8 ≤ a ∧ a + k ≤ sp ∨ sp + 24 ≤ a ∧ a + k ≤ sp + 0x1b8) (hd : Apart a k d n) :
    M'.readLE a k = M.readLE a k := by
  have hk := hP.kf
  have hout := hP.win_rt
  unfold Apart at hd
  exact hF.readLE a k (by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)

set_option maxRecDepth 20000 in
/-- **`WC` through a `memmove` into `[d, d + n)`** (held, apart from the header, inside what the function may write) -/
theorem WC.mv (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory} {d n : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp, sp + 24)] ++ [(d, d + n)]))
    (hLF : LiveFrame M M' L1 [(d, d + n)]) (hrg : M'.regions = M.regions) (hinv : R.inv b1 L1 g (view R.rt L1 M'))
    (hdhd : Apart d n st 24)
    (hdo : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st s.mem) → Outside a k [(d, d + n)])
    (hdL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(d, d + n)]) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ := by
  have hk := hP.kf
  have hstw := hP.stkF.1
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

end

end FvModexp.Amd64.ExpEven
